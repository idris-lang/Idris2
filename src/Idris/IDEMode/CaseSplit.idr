module Idris.IDEMode.CaseSplit

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.TT
import Core.Value

import Parser.Lexer.Source
import Parser.Unlit

import TTImp.Interactive.CaseSplit
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Utils

import Idris.IDEMode.TokenLine
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import Data.List
import Data.List1
import Data.List.Views
import Data.SnocList
import Libraries.Data.List.Extra
import Data.String
import System.File
import Data.Fin

%default covering

||| A series of updates is a mapping from `RawName` to `String`
||| `RawName` is currently just an alias for `String`
||| `String` is a rendered `List SourcePart`
Updates : Type
Updates = List (RawName, String)

||| Convert a RawImp update to a SourcePart one
toStrUpdate : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (Name, RawImp) -> Core Updates
toStrUpdate (UN (Basic n), term)
    = do clause <- pterm (map defaultKindedName term) -- hack
         pure [(n, show (bracket clause))]
  where
    bracket : PTerm' nm -> PTerm' nm
    bracket tm@(PRef _ _) = tm
    bracket tm@(PList _ _ _) = tm
    bracket tm@(PSnocList _ _ _) = tm
    bracket tm@(PPair _ _ _) = tm
    bracket tm@(PUnit _) = tm
    bracket tm@(PComprehension _ _ _) = tm
    bracket tm@(PPrimVal _ _) = tm
    bracket tm = PBracketed emptyFC tm
toStrUpdate _ = pure [] -- can't replace non user names

data UPD : Type where


||| Returns True if the SourcePart is a `Whitespace _` and False if not. Useful
||| for filtering or spanning a `List SourcPart`
isWhitespace : SourcePart -> Bool
isWhitespace (Whitespace _) = True
isWhitespace _              = False

||| Given a list of definitions, a list of mappings from `RawName` to `String`,
||| and a list of tokens to update, work out the updates to do, apply them, and
||| return the result.
doUpdates : {auto s : Ref Syn SyntaxInfo} ->
            {auto u : Ref UPD (List String)} ->
            Defs -> Updates -> List SourcePart ->
            Core (List SourcePart)
doUpdates defs ups [] = pure []   -- no more tokens to update, so we are done
-- if we have a name that acts as an as-pattern then do not update it
doUpdates defs ups (Name n :: AsPattern :: xs)
    = pure $ Name n :: AsPattern :: !(doUpdates defs ups xs)
-- if we have an `@{` that was not handled as a named pattern, it should not
-- result in named expansion (i.e. `@{n = ...}`) because that is not syntactically
-- valid. This clause allows us to treat `@{n}` just like `n` (no braces).
doUpdates defs ups (AsPattern :: LBrace :: xs)
    = pure $ AsPattern :: LBrace :: !(doUpdates defs ups xs)
-- if we have an LBrace (i.e. `{`), handle its contents
doUpdates defs ups (LBrace :: xs)
    -- the cases we care about are easy to detect w/o whitespace, so separate it
    = let (ws, nws) = span isWhitespace xs in
        case nws of
          -- handle potential whitespace in the other parts
          Name n :: rest =>
             let (ws', nws') = span isWhitespace rest in
               case nws' of
                  -- brace is immediately closed, so generate a new
                  -- pattern-match on the values the name can have, e.g.
                  -- { x}  where x : Nat would become { x = Z}
                  --                       (and later { x = (S k)})
                  RBrace :: rest' =>
                    pure (LBrace :: ws ++
                          Name n :: Whitespace " " :: Equal :: Whitespace " " ::
                          !(doUpdates defs ups (Name n :: ws' ++ RBrace :: rest'))
                          )
                  -- preserve whitespace before (and after) the Equal
                  Equal :: rest' =>
                    let (ws'', nws'') = span isWhitespace rest' in
                    pure (LBrace :: ws ++
                          Name n :: ws' ++ Equal :: ws'' ++
                          !(doUpdates defs ups nws'')
                          )
                  -- handle everything else as usual, preserving whitespace
                  _ => pure (LBrace :: ws ++ Name n :: ws' ++
                             !(doUpdates defs ups rest)
                             )
          -- not a special case: proceed as normal
          _ => pure (LBrace :: [] ++ !(doUpdates defs ups xs))
-- if we have a name, look up if it's a name we're updating. If it isn't, keep
-- the old name, otherwise update the name, i.e. replace with the new name
doUpdates defs ups (Name n :: xs)
    = case lookup n ups of
           Nothing => pure (Name n :: !(doUpdates defs ups xs))
           Just up => pure (Other up :: !(doUpdates defs ups xs))
-- if we have a hole, get the used names, generate+register a new unique name,
-- and change the hole's name to the new one
doUpdates defs ups (HoleName n :: xs)
    = do used <- get UPD
         n' <- uniqueHoleName defs used n
         put UPD (n' :: used)
         pure $ HoleName n' :: !(doUpdates defs ups xs)
-- if it's not a thing we update, leave it and continue working on the rest
doUpdates defs ups (x :: xs)
    = pure $ x :: !(doUpdates defs ups xs)

-- State here is a list of new hole names we generated (so as not to reuse any).
-- Update the token list with the string replacements for each match, and return
-- the newly generated strings.
updateAll : {auto s : Ref Syn SyntaxInfo} ->
            {auto u : Ref UPD (List String)} ->
            Defs -> List SourcePart -> List Updates ->
            Core (List String)
updateAll defs l [] = pure []
updateAll defs l (rs :: rss)
    = do l' <- doUpdates defs rs l
         rss' <- updateAll defs l rss
         pure (concatMap toString l' :: rss')

-- Turn the replacements we got from 'getSplits' into a list of actual string
-- replacements
getReplaces : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              List (Name, RawImp) -> Core Updates
getReplaces updates
    = do strups <- traverse toStrUpdate updates
         pure (concat strups)

showImpossible : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 (indent : Nat) -> RawImp -> Core String
showImpossible indent lhs
    = do clause <- pterm (map defaultKindedName lhs) -- hack
         pure (fastPack (replicate indent ' ') ++ show clause ++ " impossible")

||| What type of `case` block we're splitting:
||| - OneLine Nat
|||   ```
|||   f n = (case n of case_val => ?f_rhs)
|||   ```
|||   The `Nat` is the index of the "of" keyword
||| - HoleNameParen
|||   ```
|||   g n = (case n of
|||               case_val => ?g_rhs)
|||   ```
data CaseStmtType = Oneline Nat
                  | OnelineParen Nat
                  | HoleNameParen

||| Inspect the token list to see if it contains an interesting `case` block for
||| splitting, and if it does, determine the type of interesting `case` block
getCaseStmtType : (toks : List SourcePart) -> Maybe CaseStmtType
getCaseStmtType toks
  = let nws = filter (not . isWhitespace) toks in
        -- use SnocList of nws so we can express the pattern we're looking for
        -- as it would appear
        case Lin <>< nws of
             -- If the line ends with a right parenthesis followed by a
             -- `HoleName`, we're interested in what kind of `case` block it is
             start :< HoleName _ :< Other ")" =>
                  -- try to find the index of a `Name "of"` in the SnocList of
                  -- all tokens, including whitespace; if we don't find one, the
                  -- line must be a case hole on a new line, otherwise, it must
                  -- be a oneline case statement and the index let's us
                  -- calculate the indentation required!
                  case findIndex isNameOf (Lin <>< toks) of
                       Nothing => Just HoleNameParen
                       (Just skotOfIndex) =>
                            -- calculate the indentation, remembering that we
                            -- constructed a SnocList so the index is backwards
                            let ofIndex = minus (length toks) (finToNat skotOfIndex) in
                                Just $ OnelineParen (calcIndent ofIndex toks)
             -- If the line ends with a `HoleName`, check if its a oneline `case` block
             start :< HoleName _ =>
                  case findIndex isNameOf (Lin <>< toks) of
                       Nothing => Nothing
                       (Just skotOfIndex) =>
                            let ofIndex = minus (length toks) (finToNat skotOfIndex) in
                                Just $ Oneline (calcIndent ofIndex toks)
             -- If it doesn't, it's not a statement we're interested in
             _ => Nothing
    where
      isNameOf : SourcePart -> Bool
      isNameOf (Name "of") = True
      isNameOf _ = False

      calcIndent : Nat -> List SourcePart -> Nat
      calcIndent ofIndex toks
        = let (preOf, _) = splitAt ofIndex toks in
              foldr (\e,a => a + (length . toString) e) 0 preOf


||| Given a list of characters reprsenting an update string, drop its last
||| element.
dropLast : (updChars : List Char) -> List Char
dropLast updChars with (snocList updChars)
  dropLast [] | Empty = []
  dropLast (xs ++ [x]) | (Snoc x xs rec) = xs

||| Trim whitespace to the right of the string
rtrim : String -> String
rtrim = reverse . ltrim . reverse

||| Drop the closing parenthesis and any indentation preceding it.
parenTrim : String -> String
parenTrim = Idris.IDEMode.CaseSplit.rtrim . fastPack . dropLast . fastUnpack

||| Drop the number of letters equal to the indentation level to align
||| just after the `of`.
onelineIndent : Nat -> String -> String
onelineIndent indentation
  = (indent indentation) . fastPack . (drop indentation) . fastUnpack

||| An unbracketed, oneline `case` block just needs to have the last updates
||| indented to lign up with the statement after the `of`.
handleOneline : (indentation : Nat) -> (upds : List String) -> List String
handleOneline indentation [] = []
handleOneline indentation (u :: us) = u :: ((onelineIndent indentation) <$> us)

||| A bracketed, oneline `case` block needs to have the parenthesis cut off the
||| first update; all the following updates, apart from the last, need to have
||| the parenthesis cut off and be indented rather than having the line
||| repeated; the final update only needs to be indented, but must preserve the
||| parenthesis from the original line that was split.
handleOnelineParen : (indentation : Nat) -> (upds : List String) -> List String
handleOnelineParen indentation upds with (snocList upds)
  handleOnelineParen indentation [] | Empty = []
  handleOnelineParen indentation (xs ++ [x]) | (Snoc x xs rec)
    = handleMiddle xs ++ [onelineIndent indentation x]
  where
    handleMiddle : (us : List String) -> List String
    handleMiddle [] = []
    handleMiddle (u :: us)
      = (parenTrim $ onelineIndent indentation u) :: handleMiddle us

||| A `HoleName` folled by a parenthesis needs to have the parenthesis removed
||| from every update apart from the final one.
handleHoleNameParen : (upds : List String) -> List String
handleHoleNameParen upds with (snocList upds)
  handleHoleNameParen [] | Empty = []
  handleHoleNameParen (xs ++ [x]) | (Snoc x xs rec) = map parenTrim xs ++ [x]

||| Given a list of updates and some information as to what kind of `case` block
||| needs handling, change the updates such that the result is syntactically
||| correct Idris.
handleCaseStmtType : (upds : List String) ->
                     (cst : CaseStmtType) ->
                     List String
handleCaseStmtType [] _ = []
handleCaseStmtType (u :: us) (Oneline indentation) = handleOneline indentation (u :: us)
handleCaseStmtType (u :: us) (OnelineParen indentation)
  = (parenTrim u) :: handleOnelineParen indentation us
handleCaseStmtType upds HoleNameParen = handleHoleNameParen upds

||| Given a list of updates and a line and column, find the relevant line in
||| the source file and return the lines to replace it with.
export
updateCase : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ClauseUpdate -> Int -> Int ->
             Core (List String)
updateCase splits line col
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => throw (InternalError "No file loaded")
              Just f =>
                do Right file <- coreLift $ readFile f
                       | Left err => throw (FileErr f err)
                   let thisline = elemAt (lines file) (integerToNat (cast line))
                   case thisline of
                        Nothing => throw (InternalError "File too short!")
                        Just l =>
                            do let valid = mapMaybe getValid splits
                               let bad = mapMaybe getBad splits
                               log "interaction.casesplit" 3 $ "Valid: " ++ show valid
                               log "interaction.casesplit" 3 $ "Bad: " ++ show bad
                               if isNil valid
                                  then do let indent = getIndent 0 $ fastUnpack l
                                          traverse (showImpossible indent) bad
                                  else do rs <- traverse getReplaces valid
                                          let stok = tokens l
                                          defs <- get Ctxt
                                          u <- newRef UPD []
                                          upds <- updateAll defs stok rs
                                          pure $ case getCaseStmtType stok of
                                                      Nothing => upds
                                                      (Just cst) =>
                                                          handleCaseStmtType upds cst
  where
    getValid : ClauseUpdate -> Maybe (List (Name, RawImp))
    getValid (Valid _ ups) = Just ups
    getValid _ = Nothing

    getBad : ClauseUpdate -> Maybe RawImp
    getBad (Impossible lhs) = Just lhs
    getBad _ = Nothing

    getIndent : (acc : Nat) -> List Char -> Nat
    getIndent acc [] = acc
    getIndent acc (' ' :: xs) = getIndent (acc + 1) xs
    getIndent acc _ = acc

fnName : Bool -> Name -> String
fnName lhs (UN (Basic n))
    = if isIdentNormal n then n
      else if lhs then "(" ++ n ++ ")"
      else "op"
fnName lhs (NS _ n) = fnName lhs n
fnName lhs (DN s _) = s
fnName lhs n = nameRoot n


export
getClause : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            Int -> Name -> Core (Maybe String)
getClause l n
    = do defs <- get Ctxt
         Just (loc, nidx, envlen, ty) <- findTyDeclAt (\p, n => onLine (l-1) p)
             | Nothing => pure Nothing
         n <- getFullName nidx
         argns <- getEnvArgNames defs envlen !(nf defs [] ty)
         Just srcLine <- getSourceLine l
           | Nothing => pure Nothing
         let (mark, src) = isLitLine srcLine
         pure (Just (indent mark loc ++ fnName True n ++ concat (map (" " ++) argns) ++
                  " = ?" ++ fnName False n ++ "_rhs"))
  where
    indent : Maybe String -> NonEmptyFC -> String
    indent (Just mark) fc
        = relit (Just mark) $ pack (replicate (integerToNat (cast (max 0 (snd (startPos fc) - 1)))) ' ')
    indent Nothing fc = pack (replicate (integerToNat (cast (snd (startPos fc)))) ' ')
