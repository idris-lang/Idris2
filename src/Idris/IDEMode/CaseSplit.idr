module Idris.IDEMode.CaseSplit

import Core.Context
import Core.Env
import Core.Metadata
import Core.TT
import Core.Value

import Parser.Lexer.Source
import Parser.Unlit

import TTImp.Interactive.CaseSplit
import TTImp.TTImp
import TTImp.Utils

import Idris.IDEMode.TokenLine
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import Data.List
import Data.List1
import Libraries.Data.List.Extra
import Libraries.Data.String.Extra
import Data.Strings
import System.File

%hide Data.Strings.lines
%hide Data.Strings.lines'
%hide Data.Strings.unlines
%hide Data.Strings.unlines'

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
toStrUpdate (UN n, term)
    = do clause <- pterm term
         pure [(n, show (bracket clause))]
  where
    bracket : PTerm -> PTerm
    bracket tm@(PRef _ _) = tm
    bracket tm@(PList _ _) = tm
    bracket tm@(PPair _ _ _) = tm
    bracket tm@(PUnit _) = tm
    bracket tm@(PComprehension _ _ _) = tm
    bracket tm@(PPrimVal _ _) = tm
    bracket tm = PBracketed emptyFC tm
toStrUpdate _ = pure [] -- can't replace non user names

data UPD : Type where

doUpdates : {auto u : Ref UPD (List String)} ->
            Defs -> Updates -> List SourcePart ->
            Core (List SourcePart)
doUpdates defs ups [] = pure []
doUpdates defs ups (LBrace :: xs)
    = let (ws, nws) = spanSpace xs in map (LBrace :: ws ++) $
         case nws of
           Name n :: RBrace :: rest =>
                pure (Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups (Name n :: RBrace :: rest)))
           Name n :: Equal :: rest =>
                pure (Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups rest))
           _ => doUpdates defs ups xs
  where
    spanSpace : List SourcePart -> (List SourcePart, List SourcePart)
    spanSpace []                   = ([], [])
    spanSpace (RBrace           :: xs) = ([], RBrace :: xs)
    spanSpace (w@(Whitespace _) :: xs) = mapFst (w ::) (spanSpace xs)
    spanSpace (x                :: xs) = map    (x ::) (spanSpace xs)
doUpdates defs ups (Name n :: xs)
    = case lookup n ups of
           Nothing => pure (Name n :: !(doUpdates defs ups xs))
           Just up => pure (Other up :: !(doUpdates defs ups xs))
doUpdates defs ups (HoleName n :: xs)
    = do used <- get UPD
         n' <- uniqueName defs used n
         put UPD (n' :: used)
         pure $ HoleName n' :: !(doUpdates defs ups xs)
doUpdates defs ups (x :: xs)
    = pure $ x :: !(doUpdates defs ups xs)

-- State here is a list of new hole names we generated (so as not to reuse any).
-- Update the token list with the string replacements for each match, and return
-- the newly generated strings.
updateAll : {auto u : Ref UPD (List String)} ->
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
                 RawImp -> Core String
showImpossible lhs
    = do clause <- pterm lhs
         pure (show clause ++ " impossible")

-- Given a list of updates and a line and column, find the relevant line in
-- the source file and return the lines to replace it with
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
                   let thisline = elemAt (forget $ lines file) (integerToNat (cast line))
                   case thisline of
                        Nothing => throw (InternalError "File too short!")
                        Just l =>
                            do let valid = mapMaybe getValid splits
                               let bad = mapMaybe getBad splits
                               if isNil valid
                                  then traverse showImpossible bad
                                  else do rs <- traverse getReplaces valid
                                          let stok = tokens l
                                          defs <- get Ctxt
                                          u <- newRef UPD (the (List String) [])
                                          updateAll defs stok rs
  where
    getValid : ClauseUpdate -> Maybe (List (Name, RawImp))
    getValid (Valid _ ups) = Just ups
    getValid _ = Nothing

    getBad : ClauseUpdate -> Maybe RawImp
    getBad (Impossible lhs) = Just lhs
    getBad _ = Nothing

fnName : Bool -> Name -> String
fnName lhs (UN n)
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
