module Idris.REPL

import Compiler.Common
import Compiler.Inline

import Core.Case.CaseTree
import Core.CompileExpr
import Core.CompileExpr.Pretty
import Core.Context
import Core.Context.Log
import Core.Context.Pretty
import Core.Directory
import Core.Env
import Core.FC
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.TT.Views
import Core.Termination
import Core.Unify
import Core.Value

import Core.SchemeEval

import Parser.Unlit

import Idris.CommandLine
import Idris.Desugar
import Idris.Doc.Display
import Idris.Doc.String
import Idris.Error
import Idris.IDEMode.CaseSplit
import Idris.IDEMode.Commands
import Idris.IDEMode.MakeClause
import Idris.IDEMode.Holes
import Idris.ModTree
import Idris.Parser
import Idris.Pretty
import Idris.ProcessIdr
import Idris.Resugar
import Idris.Syntax
import Idris.Version

import public Idris.REPL.Common
import Idris.REPL.FuzzySearch

import TTImp.TTImp.Functor
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Local
import TTImp.Interactive.CaseSplit
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Interactive.Intro
import TTImp.Interactive.MakeLemma
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils
import TTImp.BindImplicits
import TTImp.ProcessDecls

import Data.List
import Data.List1
import Data.Maybe
import Libraries.Data.NameMap
import Libraries.Data.PosMap
import Data.Stream
import Data.String
import Libraries.Data.List.Extra
import Libraries.Data.SparseMatrix
import Libraries.Data.String.Extra
import Libraries.Data.Tap
import Libraries.Data.WithDefault
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Utils.Path
import Libraries.System.Directory.Tree

import System
import System.File

%default covering

-- Do NOT remove: it can be used instead of prettyInfo in case the prettier output
-- happens to be buggy
showInfo : {auto c : Ref Ctxt Defs} ->
           (Name, Int, GlobalDef) -> Core ()
showInfo (n, idx, d)
    = do coreLift_ $ putStrLn (show (fullname d) ++ " ==> " ++
                              show !(toFullNames (definition d)))
         coreLift_ $ putStrLn (show (multiplicity d))
         coreLift_ $ putStrLn ("Erasable args: " ++ show (eraseArgs d))
         coreLift_ $ putStrLn ("Detaggable arg types: " ++ show (safeErase d))
         coreLift_ $ putStrLn ("Specialise args: " ++ show (specArgs d))
         coreLift_ $ putStrLn ("Inferrable args: " ++ show (inferrable d))
         whenJust (compexpr d) $ \ expr =>
           coreLift_ $ putStrLn ("Compiled: " ++ show expr)
         coreLift_ $ putStrLn ("Refers to: " ++
                               show !(traverse getFullName (keys (refersTo d))))
         coreLift_ $ putStrLn ("Refers to (runtime): " ++
                               show !(traverse getFullName (keys (refersToRuntime d))))
         coreLift_ $ putStrLn ("Flags: " ++ show (flags d))
         when (not (isNil (sizeChange d))) $
            let scinfo = map (\s => show (fnCall s) ++ ": " ++
                                    show (fnArgs s)) !(traverse toFullNames (sizeChange d)) in
                coreLift_ $ putStrLn $
                        "Size change: " ++ showSep ", " scinfo

prettyInfo : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             (Name, Int, GlobalDef) -> Core (Doc IdrisDocAnn)
prettyInfo (n, idx, d)
    = do let nm = fullname d
         def <- toFullNames (definition d)
         referCT <- traverse getFullName (keys (refersTo d))
         referRT <- traverse getFullName (keys (refersToRuntime d))
         schanges <- traverse toFullNames $ sizeChange d
         pp <- getPPrint
         setPPrint ({ showMachineNames := True } pp)
         def <- Resugared.prettyDef def
         setPPrint ({ showMachineNames := showMachineNames pp } pp)
         pure $ vcat $
           [ reAnnotate Syntax (prettyRig $ multiplicity d) <+> showCategory Syntax d (pretty0 nm)
           , def
           ] ++
           catMaybes
           [ (\ args => header "Erasable args" <++> byShow args) <$> ifNotNull (eraseArgs d)
           , (\ args => header "Detaggable arg types" <++> byShow args) <$> ifNotNull (safeErase d)
           , (\ args => header "Specialise args" <++> byShow args) <$> ifNotNull (specArgs d)
           , (\ args => header "Inferrable args" <++> byShow args) <$> ifNotNull (inferrable d)
           , (\ expr => header "Compiled" <++> pretty expr) <$> compexpr d
           , (\ nms  => header "Refers to" <++> enum pretty0 nms) <$> ifNotNull referCT
           , (\ nms  => header "Refers to (runtime)" <++> enum pretty0 nms) <$> ifNotNull referRT
           , (\ flgs => header "Flags" <++> enum byShow flgs) <$> ifNotNull (flags d)
           , (\ sz   => header "Size change" <+> hardline <+> indent 2 (displayChg sz)) <$> ifNotNull schanges
           ]

  where
    ifNotNull : List a -> Maybe (List a)
    ifNotNull xs = xs <$ guard (not $ null xs)

    enum : (a -> Doc IdrisDocAnn) -> List a -> Doc IdrisDocAnn
    enum p xs = hsep $ punctuate "," $ p <$> xs

    enumLine : (a -> Doc IdrisDocAnn) -> List a -> Doc IdrisDocAnn
    enumLine p xs = hcat $ punctuate hardline $ p <$> xs

    displayChg : List SCCall -> Doc IdrisDocAnn
    displayChg sz =
      let scinfo = \s => pretty0 (fnCall s) <+> ":" <+> hardline <+> cast (prettyTable "r" "l" 1 (fnArgs s)) in
      enumLine scinfo sz

getEnvTerm : {vars : _} ->
             List Name -> Env Term vars -> Term vars ->
             (vars' ** (Env Term vars', Term vars'))
getEnvTerm (n :: ns) env (Bind fc x b sc)
    = if n == x
         then getEnvTerm ns (b :: env) sc
         else (_ ** (env, Bind fc x b sc))
getEnvTerm _ env tm = (_ ** (env, tm))

displayPatTerm : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Defs -> ClosedTerm ->
                 Core String
displayPatTerm defs tm
    = do ptm <- resugarNoPatvars Env.empty !(normaliseHoles defs Env.empty tm)
         pure (show ptm)

setOpt : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         REPLOpt -> Core ()
setOpt (ShowImplicits t)
    = do pp <- getPPrint
         setPPrint ({ showImplicits := t } pp)
setOpt (ShowNamespace t)
    = do pp <- getPPrint
         setPPrint ({ fullNamespace := t } pp)
setOpt (ShowMachineNames t)
    = do pp <- getPPrint
         setPPrint ({ showMachineNames := t } pp)
setOpt (ShowTypes t)
    = update ROpts { showTypes := t }
setOpt (EvalMode m)
    = update ROpts { evalMode := m }
setOpt (Editor e)
    = update ROpts { editor := e }
setOpt (CG e)
    = do defs <- get Ctxt
         case getCG (options defs) e of
            Just cg => setCG cg
            Nothing => iputStrLn (reflow "No such code generator available")
setOpt (Profile t)
    = do pp <- getSession
         setSession ({ profile := t } pp)
setOpt (EvalTiming t)
    = setEvalTiming t

getOptions : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         Core (List REPLOpt)
getOptions = do
  pp <- getPPrint
  opts <- get ROpts
  pure $ [ ShowImplicits (showImplicits pp), ShowMachineNames (showMachineNames pp)
         , ShowNamespace (fullNamespace pp)
         , ShowTypes (showTypes opts), EvalMode (evalMode opts)
         , Editor (editor opts)
         ]

anyAt : (a -> Bool) -> a -> b -> Bool
anyAt p loc _ = p loc

printClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Maybe String -> Nat -> ImpClause ->
              Core String
printClause l i (PatClause _ lhsraw rhsraw)
    = do lhs <- pterm $ map defaultKindedName lhsraw -- hack
         rhs <- pterm $ map defaultKindedName rhsraw -- hack
         pure (relit l (pack (replicate i ' ') ++ show lhs ++ " = " ++ show rhs))
printClause l i (WithClause _ lhsraw rig wvraw prf flags csraw)
    = do lhs <- pterm $ map defaultKindedName lhsraw -- hack
         wval <- pterm $ map defaultKindedName wvraw -- hack
         cs <- traverse (printClause l (i + 2)) csraw
         pure (relit l (pack (replicate i ' ')
                ++ show lhs
                ++ " with " ++ showCount rig ++ "(" ++ show wval ++ ")"
                   -- TODO: remove `the` after fix idris-lang/Idris2#3418
                ++ maybe "" (the (_ -> _) $ \(rg, nm) => " proof " ++ showCount rg ++ show nm) prf
                ++ "\n")
               ++ showSep "\n" cs)
printClause l i (ImpossibleClause _ lhsraw)
    = do lhs <- pterm $ map defaultKindedName lhsraw -- hack
         pure (relit l (pack (replicate i ' ') ++ show lhs ++ " impossible"))


lookupDefTyName : Name -> Context ->
                  Core (List (Name, Int, (Def, ClosedTerm)))
lookupDefTyName = lookupNameBy (\g => (definition g, type g))

updateFile : {auto r : Ref ROpts REPLOpts} ->
             (List String -> List String) -> Core EditResult
updateFile update
    = do opts <- get ROpts
         let Just f = mainfile opts
             | Nothing => pure (DisplayEdit emptyDoc) -- no file, nothing to do
         Right content <- coreLift $ readFile f
               | Left err => throw (FileErr f err)
         coreLift_ $ writeFile (f ++ "~") content
         coreLift_ $ writeFile f (unlines (update (lines content)))
         pure (DisplayEdit emptyDoc)

rtrim : String -> String
rtrim str = reverse (ltrim (reverse str))

addClause : String -> Nat -> List String -> List String
addClause c Z [] = rtrim c :: []
addClause c Z (x :: xs)
    = if all isSpace (unpack x)
         then rtrim c :: x :: xs
         else x :: addClause c Z xs
addClause c (S k) (x :: xs) = x :: addClause c k xs
addClause c (S k) [] = [c]

caseSplit : String -> Nat -> List String -> List String
caseSplit c Z (x :: xs) = rtrim c :: xs
caseSplit c (S k) (x :: xs) = x :: caseSplit c k xs
caseSplit c _ [] = [c]

proofSearch : Name -> String -> Nat -> List String -> List String
proofSearch n res Z (x :: xs) = replaceStr ("?" ++ show n) res x :: xs
  where
    replaceStr : String -> String -> String -> String
    replaceStr rep new "" = ""
    replaceStr rep new str
        = if isPrefixOf rep str
             then new ++ pack (drop (length rep) (unpack str))
             else assert_total $ strCons (prim__strHead str)
                          (replaceStr rep new (prim__strTail str))
proofSearch n res (S k) (x :: xs) = x :: proofSearch n res k xs
proofSearch n res _ [] = []

addMadeLemma : Maybe String -> Name -> String -> String -> Nat -> List String -> List String
addMadeLemma lit n ty app line content
    = addApp lit line [] (proofSearch n app line content)
  where
    -- Put n : ty in the first blank line
    insertInBlank : Maybe String -> List String -> List String
    insertInBlank lit [] = [relit lit $ show n ++ " : " ++ ty ++ "\n"]
    insertInBlank lit (x :: xs)
        = if trim x == ""
             then ("\n" ++ (relit lit $ show n ++ " : " ++ ty ++ "\n")) :: xs
             else x :: insertInBlank lit xs

    addApp : Maybe String -> Nat -> List String -> List String -> List String
    addApp lit Z acc rest = reverse (insertInBlank lit acc) ++ rest
    addApp lit (S k) acc (x :: xs) = addApp lit k (x :: acc) xs
    addApp _ (S k) acc [] = reverse acc

-- Replace a line; works for 'case' and 'with'
addMadeCase : Maybe String -> List String -> Nat -> List String -> List String
addMadeCase lit wapp line content
    = addW line [] content
  where
    addW : Nat -> List String -> List String -> List String
    addW Z acc (_ :: rest) = reverse acc ++ map (relit lit) wapp ++ rest
    addW Z acc [] = [] -- shouldn't happen!
    addW (S k) acc (x :: xs) = addW k (x :: acc) xs
    addW (S k) acc [] = reverse acc

nextProofSearch : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  Core (Maybe (Name, RawImp))
nextProofSearch
    = do opts <- get ROpts
         let Just (n, res) = psResult opts
              | Nothing => pure Nothing
         Just (res, next) <- nextResult res
              | Nothing =>
                    do put ROpts ({ psResult := Nothing } opts)
                       pure Nothing
         put ROpts ({ psResult := Just (n, next) } opts)
         pure (Just (n, res))

nextGenDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto o : Ref ROpts REPLOpts} ->
             (reject : Nat) ->
             Core (Maybe (Int, (FC, List ImpClause)))
nextGenDef reject
    = do opts <- get ROpts
         let Just (line, res) = gdResult opts
              | Nothing => pure Nothing
         Just (res, next) <- nextResult res
              | Nothing =>
                    do put ROpts ({ gdResult := Nothing } opts)
                       pure Nothing
         put ROpts ({ gdResult := Just (line, next) } opts)
         case reject of
              Z => pure (Just (line, res))
              S k => nextGenDef k

dropLams : Nat -> RawImp' nm -> RawImp' nm
dropLams Z tm = tm
dropLams (S k) (ILam _ _ _ _ _ sc) = dropLams k sc
dropLams _ tm = tm

dropLamsTm : {vars : _} ->
             Nat -> Env Term vars -> Term vars ->
             (vars' ** (Env Term vars', Term vars'))
dropLamsTm Z env tm = (_ ** (env, tm))
dropLamsTm (S k) env (Bind _ _ b sc) = dropLamsTm k (b :: env) sc
dropLamsTm _ env tm = (_ ** (env, tm))

findInTree : FilePos -> Name -> PosMap (NonEmptyFC, Name) -> Maybe Name
findInTree p hint m
  = map snd $ head'
  $ sortBy (cmp `on` measure)
  $ filter match
  $ searchPos p m

  where
    cmp : FileRange -> FileRange -> Ordering
    cmp ((sr1, sc1), (er1, ec1)) ((sr2, sc2), (er2, ec2)) =
      compare (er1 - sr1, ec1 - sc1) (er2 - sr2, ec2 - sc2)

    checkAsNamespace : String -> Name -> Bool
    checkAsNamespace i (NS ns' n) = i `isInPathOf` ns'
    checkAsNamespace _ _ = False

    startsWithUpper : String -> Bool
    startsWithUpper str = case strM str of
       StrNil => False
       StrCons c _ => isUpper c || c > chr 160

    matchingRoots : Name -> Name -> Bool
    matchingRoots = (==) `on` nameRoot

    checkCandidate : Name -> Bool
    checkCandidate cand = matchingRoots hint cand || case hint of
      -- a basic user name: may actually be e.g. the `B` part of `A.B.C.val`
      UN (Basic n) => startsWithUpper n && checkAsNamespace n cand
      _ => False

    match : (NonEmptyFC, Name) -> Bool
    match (_, n) = matches hint n && checkCandidate n

record TermWithType (vars : Scope) where
  constructor WithType
  termOf : Term vars
  typeOf : Term vars

getItDecls :
    {auto o : Ref ROpts REPLOpts} ->
    Core (List ImpDecl)
getItDecls
    = do opts <- get ROpts
         case evalResultName opts of
            Nothing => pure []
            Just n =>
              let it = UN $ Basic "it" in
              pure [ IClaim
                       (MkFCVal replFC $ MkIClaimData top Private []
                                       $ MkImpTy replFC (NoFC it) (Implicit replFC False))
                  , IDef replFC it [PatClause replFC (IVar replFC it) (IVar replFC n)]]

||| Produce the elaboration of a PTerm, along with its inferred type
inferAndElab :
  {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto u : Ref UST UState} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto m : Ref MD Metadata} ->
  {auto o : Ref ROpts REPLOpts} ->
  ElabMode ->
  PTerm ->
  Env Term vars ->
  Core (TermWithType vars)
inferAndElab emode itm env
  = do ttimp <- desugar AnyExpr (toList vars) itm
       let ttimpWithIt = ILocal replFC !getItDecls ttimp
       inidx <- resolveName (UN $ Basic "[input]")
       -- a TMP HACK to prioritise list syntax for List: hide
       -- foreign argument lists. TODO: once the new FFI is fully
       -- up and running we won't need this. Also, if we add
       -- 'with' disambiguation we can use that instead.
       catch (do hide replFC (NS primIONS (UN $ Basic "::"))
                 hide replFC (NS primIONS (UN $ Basic "Nil")))
             (\err => pure ())
       (tm , gty) <- elabTerm inidx emode [] (MkNested []) env ttimpWithIt Nothing
       ty <- getTerm gty
       pure (tm `WithType` ty)

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core EditResult
processEdit (TypeAt line col name)
    = do defs <- get Ctxt
         meta <- get MD

         -- Search the correct name by location for more precise search
         -- and fallback to given name if nothing found
         let name = fromMaybe name
                  $ findInTree (line-1, col) name (nameLocMap meta)

         -- Lookup the name globally
         globals <- lookupCtxtName name (gamma defs)

         -- Get the Doc for the result
         globalResult <- case globals of
           [] => pure Nothing
           ts => do tys <- traverse (displayType False defs) ts
                    pure $ Just (vsep $ map (reAnnotate Pretty.Syntax) tys)

         -- Lookup the name locally (The name at the specified position)
         localResult <- findTypeAt $ anyAt $ within (line-1, col)

         case (globalResult, localResult) of
              -- Give precedence to the local name, as it shadows the others
              (_, Just (n, _, type)) => pure $ DisplayEdit $
                prettyLocalName n <++> colon <++> !(reAnnotate Syntax <$> displayTerm defs type)
              (Just globalDoc, Nothing) => pure $ DisplayEdit $ globalDoc
              (Nothing, Nothing) => undefinedName replFC name

  where

    prettyLocalName : Name -> Doc IdrisAnn
    -- already looks good
    prettyLocalName nm@(UN _) = pretty0 nm
    prettyLocalName nm@(NS _ (UN _)) = pretty0 nm
    -- otherwise
    prettyLocalName nm = case userNameRoot nm of
      -- got rid of `Nested` or `PV`
      Just nm => pretty0 nm
      -- really bad case e.g. case block name
      Nothing => pretty0 (nameRoot nm)

processEdit (CaseSplit upd line col name)
    = do let find = if col > 0
                       then within (line-1, col-1)
                       else onLine (line-1)
         OK splits <- getSplits (anyAt find) name
             | SplitFail err => pure (EditError (pretty0 $ show err))
         lines <- updateCase splits (line-1) (col-1)
         if upd
            then updateFile (caseSplit (unlines lines) (integerToNat (cast (line - 1))))
            else pure $ DisplayEdit (vsep $ pretty0 <$> lines)
processEdit (AddClause upd line name)
    = do Just c <- getClause line name
             | Nothing => pure (EditError (pretty0 name <++> reflow "not defined here"))
         if upd
            then updateFile (addClause c (integerToNat (cast line)))
            else pure $ DisplayEdit (pretty0 c)
processEdit (Intro upd line hole)
    = do defs <- get Ctxt
         -- Grab the hole's definition (and check it is not a solved hole)
         [(h, hidx, hgdef)] <- lookupCtxtName hole (gamma defs)
           | _ => pure $ EditError ("Could not find hole named" <++> pretty0 hole)
         let Hole args _ = definition hgdef
           | _ => pure $ EditError (pretty0 hole <++> "is not a refinable hole")
         let (lhsCtxt ** (env, htyInLhsCtxt)) = underPis (cast args) Env.empty (type hgdef)

         (iintrod :: iintrods) <- intro hidx hole env htyInLhsCtxt
           | [] => pure $ EditError "Don't know what to do."
         pintrods <- traverseList1 pterm (iintrod ::: iintrods)
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) hole (bracketholes syn)
         let introds = map (show . pretty . ifThenElse brack (addBracket replFC) id) pintrods

         if upd
            then case introds of
                   introd ::: [] => updateFile (proofSearch hole introd (integerToNat (cast (line - 1))))
                   _ => pure $ EditError "Don't know what to do"
            else pure $ MadeIntro introds
processEdit (Refine upd line hole e)
    = do defs <- get Ctxt
         -- First we grab the hole's definition (and check it is not a solved hole)
         -- We grab the LHS it lives in as well as its type in that context.
         [(h, hidx, hgdef)] <- lookupCtxtName hole (gamma defs)
           | _ => pure $ EditError ("Could not find hole named" <++> pretty0 hole)
         let Hole args _ = definition hgdef
           | _ => pure $ EditError (pretty0 hole <++> "is not a refinable hole")
         let (lhsCtxt ** (env, htyInLhsCtxt)) = underPis (cast args) Env.empty (type hgdef)

         -- Then we elaborate the expression we were given and infer its type.
         -- We have some magic built-in if the expression happens to be a single identifier
         -- corresponding to a top-level definition
         Right msize_tele_fun <- case e of
             PRef fc v => do
               (n :: ns) <- lookupCtxtName v (gamma defs)
                 -- could not find the variable: it may be a local one!
                 | [] => pure (Right Nothing)
               let sizes = (n ::: ns) <&> \ (_,_,gdef) =>
                              let ctxt = underPis (-1) Env.empty (type gdef) in
                              lengthExplicitPi $ fst $ snd $ ctxt
               let True = all (head sizes ==) sizes
                 | _ => pure (Left ("Ambiguous name" <++> pretty0 v <++> "(couldn't infer arity)"))
               let arity = args + head sizes -- pretending the term has been elaborated in the LHS context
               pure (Right $ Just arity)
             _ => pure (Right Nothing)
           | Left err => pure (EditError err)
         -- We do it in an extended context corresponding to the hole's so that users
         -- may mention variables bound on the LHS.
         size_tele_fun <- case msize_tele_fun of
             Just n => pure n
             Nothing => do
               ust <- get UST
               syn <- get Syn
               md <- get MD
               defs <- branch
               infered <- inferAndElab InExpr e env
               put UST ust
               put Syn syn
               put MD md
               put Ctxt defs
               let tele = underPis (-1) env $ typeOf infered
               pure (lengthExplicitPi $ fst $ snd tele)

         -- Now that we have a hole & a function to use inside it,
         -- we need to figure out how many arguments to pass to the function so that the types align

         -- E.g. refining `?hole : Nat` with the function `plus : Nat -> Nat -> Nat`
         -- means we need to replace the hole with `plus ?hole_1 ?hole_2`
         -- while refining it with the constructor `Z : Nat` means we can just return `Z`.

         -- Crude heuristics: measure the length of both *explicit* telescopes and pass
         -- |tele_fun| - |tele_hole| arguments.
         -- This may not always work because
         -- e.g.         fun   : (a : Type) -> {n : Nat} -> Vect n a
         -- won't fit in ?hole : (a : Type) -> Vect 3 a
         -- without eta-expansion to (\ a => fun a)
         -- It is hopefully a good enough approximation for now. A very ambitious approach
         -- would be to type-align the telescopes. Bonus points for allowing permutations.
         let size_tele_hole = lengthExplicitPi $ fst $ snd $ underPis (-1) Env.empty (type hgdef)
         let True = size_tele_fun >= size_tele_hole
           | _ => pure $ EditError $ hsep
                       [ "Cannot seem to refine", pretty0 hole
                       , "by", pretty0 (show e) ]

         -- We now have all the necessary information to manufacture the function call
         -- that starts with the expression the user passed
         call <- do -- We're forming the PTerm (e ?hole_1 ... ?hole_|missing_args|)
                    -- We don't reuse etm because it may have been elaborated to something dodgy
                    -- because of defaulting instances.
                    let n = minus size_tele_fun size_tele_hole
                    ns <- uniqueHoleNames defs n (nameRoot hole)
                    let new_holes = PHole replFC True <$> ns
                    let pcall = papply replFC e new_holes

                    -- We're desugaring it to the corresponding TTImp
                    icall <- desugar AnyExpr (lhsCtxt <>> []) pcall

                    -- We're checking this term full of holes against the type of the hole
                    -- TODO: branch before checking the expression fits
                    --       so that we can cleanly recover in case of error
                    let gty = gnf env htyInLhsCtxt
                    ccall <- checkTerm hidx {-is this correct?-} InExpr [] (MkNested []) env icall gty

                    -- And then we normalise, unelab, resugar the resulting term so
                    -- that solved holes are replaced with their solutions
                    -- (we need to re-read the context because elaboration may have added solutions to it)
                    defs <- get Ctxt
                    ncall <- normaliseHoles defs env ccall
                    pcall <- resugar env ncall
                    syn <- get Syn
                    let brack = elemBy (\x, y => dropNS x == dropNS y) hole (bracketholes syn)
                    pure $ show $ ifThenElse brack (addBracket replFC) id pcall

         if upd
            then updateFile (proofSearch hole call (integerToNat (cast (line - 1))))
            else pure $ DisplayEdit (pretty0 call)

processEdit (ExprSearch upd line name hints)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefName name (gamma defs)) of
              [(n, nidx, Hole locs _)] =>
                  do let searchtm = exprSearch replFC name hints
                     update ROpts { psResult := Just (name, searchtm) }
                     Just (_, restm) <- nextProofSearch
                          | Nothing => pure $ EditError "No search results"
                     let tm' = dropLams locs restm
                     itm <- pterm $ map defaultKindedName tm' -- hack
                     let itm'  = ifThenElse brack (addBracket replFC itm) itm
                     if upd
                        then updateFile (proofSearch name (show itm') (integerToNat (cast (line - 1))))
                        else pure $ DisplayEdit (prettyBy Syntax itm')
              [(n, nidx, PMDef pi [] (STerm _ tm) _ _)] =>
                  case holeInfo pi of
                       NotHole => pure $ EditError "Not a searchable hole"
                       SolvedHole locs =>
                          do let (_ ** (env, tm')) = dropLamsTm locs Env.empty !(normaliseHoles defs Env.empty tm)
                             itm <- resugar env tm'
                             let itm'= ifThenElse brack (addBracket replFC itm) itm
                             if upd
                                then updateFile (proofSearch name (show itm') (integerToNat (cast (line - 1))))
                                else pure $ DisplayEdit (prettyBy Syntax itm')
              [] => pure $ EditError $ "Unknown name" <++> pretty0 name
              _ => pure $ EditError "Not a searchable hole"
processEdit ExprSearchNext
    = do defs <- get Ctxt
         syn <- get Syn
         Just (name, restm) <- nextProofSearch
              | Nothing => pure $ EditError "No more results"
         [(n, nidx, Hole locs _)] <- lookupDefName name (gamma defs)
              | _ => pure $ EditError "Not a searchable hole"
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         let tm' = dropLams locs restm
         itm <- pterm $ map defaultKindedName tm'
         let itm' = ifThenElse brack (addBracket replFC itm) itm
         pure $ DisplayEdit (prettyBy Syntax itm')

processEdit (GenerateDef upd line name rej)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine (line - 1) p)
             | Nothing => pure (EditError ("Can't find declaration for" <++> pretty0 name
                                          <++> "on line" <++> byShow line))
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                 do let searchdef = makeDefSort (\p, n => onLine (line - 1) p)
                                                16 mostUsed n'
                    update ROpts { gdResult := Just (line, searchdef) }
                    Just (_, (fc, cs)) <- nextGenDef rej
                         | Nothing => pure (EditError "No search results")

                    let l : Nat = integerToNat $ cast $ startCol (toNonEmptyFC fc)

                    Just srcLine <- getSourceLine line
                       | Nothing => pure (EditError "Source line not found")
                    let (markM, srcLineUnlit) = isLitLine srcLine
                    ls <- traverse (printClause markM l) cs
                    if upd
                       then updateFile (addClause (unlines ls) (integerToNat (cast line)))
                       else pure $ DisplayEdit (vsep $ pretty0 <$> ls)
              Just _ => pure $ EditError "Already defined"
              Nothing => pure $ EditError $ "Can't find declaration for" <++> pretty0 name
processEdit GenerateDefNext
    = do Just (line, (fc, cs)) <- nextGenDef 0
              | Nothing => pure (EditError "No more results")
         let l : Nat = integerToNat $ cast $ startCol (toNonEmptyFC fc)
         Just srcLine <- getSourceLine line
            | Nothing => pure (EditError "Source line not found")
         let (markM, srcLineUnlit) = isLitLine srcLine
         ls <- traverse (printClause markM l) cs
         pure $ DisplayEdit (vsep $ pretty0 <$> ls)
processEdit (MakeLemma upd line name)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefTyName name (gamma defs)) of
              [(n, nidx, Hole locs _, ty)] =>
                  do (lty, lapp) <- makeLemma replFC name locs ty
                     pty <- pterm $ map defaultKindedName lty -- hack
                     papp <- pterm $ map defaultKindedName lapp -- hack
                     let pappstr = show (ifThenElse brack
                                            (addBracket replFC papp)
                                            papp)
                     Just srcLine <- getSourceLine line
                       | Nothing => pure (EditError "Source line not found")
                     let (markM,_) = isLitLine srcLine
                     if upd
                        then updateFile (addMadeLemma markM name (show pty) pappstr
                                                      (max 0 (integerToNat (cast (line - 1)))))
                        else pure $ MadeLemma markM name pty pappstr
              _ => pure $ EditError "Can't make lifted definition"
processEdit (MakeCase upd line name)
    = do litStyle <- getLitStyle
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         Just src <- getSourceLine line
              | Nothing => pure (EditError "Source line not available")
         let Right l = unlit litStyle src
              | Left err => pure (EditError "Invalid literate Idris")
         let (markM, _) = isLitLine src
         let c = lines $ makeCase brack name l
         if upd
            then updateFile (addMadeCase markM c (max 0 (integerToNat (cast (line - 1)))))
            else pure $ MadeCase markM c
processEdit (MakeWith upd line name)
    = do litStyle <- getLitStyle
         Just src <- getSourceLine line
              | Nothing => pure (EditError "Source line not available")
         let Right l = unlit litStyle src
              | Left err => pure (EditError "Invalid literate Idris")
         let (markM, _) = isLitLine src
         let w = lines $ makeWith name l
         if upd
            then updateFile (addMadeCase markM w (max 0 (integerToNat (cast (line - 1)))))
            else pure $ MadeWith markM w

prepareExp :
    {auto c : Ref Ctxt Defs} ->
    {auto u : Ref UST UState} ->
    {auto s : Ref Syn SyntaxInfo} ->
    {auto m : Ref MD Metadata} ->
    {auto o : Ref ROpts REPLOpts} ->
    PTerm -> Core ClosedTerm
prepareExp ctm
    = do ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN $ Basic "unsafePerformIO")) ctm)
         let ttimpWithIt = ILocal replFC !getItDecls ttimp
         inidx <- resolveName (UN $ Basic "[input]")
         (tm, ty) <- elabTerm inidx InExpr [] (MkNested [])
                                 Env.empty ttimpWithIt Nothing
         tm_erased <- linearCheck replFC linear True Env.empty tm
         compileAndInlineAll
         pure tm_erased

processLocal : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ElabOpt ->
             NestedNames vars -> Env Term vars ->
             List ImpDecl -> (scope : List ImpDecl) ->
             Core ()
processLocal {vars} eopts nest env nestdecls_in scope
    = localHelper nest env nestdecls_in $ \nest' => traverse_ (processDecl eopts nest' env) scope

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          PTerm -> Core REPLResult
execExp ctm
    = do Just cg <- findCG
           | Nothing =>
              do iputStrLn (reflow "No such code generator available")
                 pure CompilationFailed
         tm_erased <- prepareExp ctm
         logTimeWhen !getEvalTiming 0 "Execution" $
           execute cg tm_erased
         pure $ Executed ctm


execDecls : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            List PDecl -> Core REPLResult
execDecls decls = do
  traverse_ execDecl decls
  pure DefDeclared
  where
    execDecl : PDecl -> Core ()
    execDecl decl = do
      i <- desugarDecl [] decl
      inidx <- resolveName (UN $ Basic "[defs]")
      _ <- newRef EST (initEStateSub inidx Env.empty Refl)
      processLocal [] (MkNested []) Env.empty !getItDecls i

export
compileExp : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto m : Ref MD Metadata} ->
             {auto o : Ref ROpts REPLOpts} ->
             PTerm -> String -> Core REPLResult
compileExp ctm outfile
    = do Just cg <- findCG
              | Nothing =>
                   do iputStrLn (reflow "No such code generator available")
                      pure CompilationFailed
         tm_erased <- prepareExp ctm
         ok <- compile cg tm_erased outfile
         maybe (pure CompilationFailed)
               (pure . Compiled)
               ok

export
loadMainFile : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               String -> Core REPLResult
loadMainFile f
    = do update ROpts { evalResultName := Nothing }
         modIdent <- ctxtPathToNS f
         resetContext (PhysicalIdrSrc modIdent)
         Right res <- coreLift (readFile f)
            | Left err => do setSource ""
                             pure (ErrorLoadingFile f err)
         errs <- logTime 1 "Build deps" $ buildDeps f
         updateErrorLine errs
         setSource res
         resetProofState
         case errs of
           [] => pure (FileLoaded f)
           _ => pure (ErrorsBuildingFile f errs)

||| Given a REPLEval mode for evaluation,
||| produce the normalization function that normalizes terms
||| using that evaluation mode
replEval : {auto c : Ref Ctxt Defs} ->
  {vs : _} ->
  REPLEval -> Defs -> Env Term vs -> Term vs -> Core (Term vs)
replEval NormaliseAll = normaliseOpts ({ strategy := CBV } withAll)
replEval _ = normalise

||| Produce the normal form of a PTerm, along with its inferred type
inferAndNormalize : {auto c : Ref Ctxt Defs} ->
  {auto u : Ref UST UState} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto m : Ref MD Metadata} ->
  {auto o : Ref ROpts REPLOpts} ->
  REPLEval ->
  PTerm ->
  Core (TermWithType Scope.empty)
inferAndNormalize emode itm
  = do (tm `WithType` ty) <- inferAndElab (elabMode emode) itm Env.empty
       logTerm "repl.eval" 10 "Elaborated input" tm
       defs <- get Ctxt
       let norm = replEval emode
       ntm <- norm defs Env.empty tm
       logTermNF "repl.eval" 5 "Normalised" Env.empty ntm
       pure $ ntm `WithType` ty
  where
    elabMode : REPLEval -> ElabMode
    elabMode EvalTC = InType
    elabMode _ = InExpr


||| Process a single `REPLCmd`
|||
||| Returns `REPLResult` for display by the higher level shell which
||| is invoking this interactive command processing.
export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          REPLCmd -> Core REPLResult
process (NewDefn decls) = execDecls decls
process (Eval itm)
    = do opts <- get ROpts
         let emode = evalMode opts
         case emode of
            Execute => do ignore (execExp itm); pure (Executed itm)
            Scheme =>
              do (tm `WithType` ty) <- inferAndElab InExpr itm Env.empty
                 qtm <- logTimeWhen !getEvalTiming 0 "Evaluation" $
                           (do nf <- snfAll Env.empty tm
                               quote Env.empty nf)
                 itm <- logTimeWhen False 0 "Resugar" $ resugar Env.empty qtm
                 pure (Evaluated itm Nothing)
            _ =>
              do (ntm `WithType` ty) <- logTimeWhen !getEvalTiming 0 "Evaluation" $
                                           inferAndNormalize emode itm
                 itm <- resugar Env.empty ntm
                 defs <- get Ctxt
                 opts <- get ROpts
                 let norm = replEval emode
                 evalResultName <- DN "it" <$> genName "evalResult"
                 ignore $ addDef evalResultName
                   $ newDef replFC evalResultName top Scope.empty ty defaulted
                   $ PMDef defaultPI Scope.empty (STerm 0 ntm) (STerm 0 ntm) []
                 addToSave evalResultName
                 put ROpts ({ evalResultName := Just evalResultName } opts)
                 if showTypes opts
                    then do ity <- resugar Env.empty !(norm defs Env.empty ty)
                            pure (Evaluated itm (Just ity))
                    else pure (Evaluated itm Nothing)
process (Check (PRef fc (UN (Basic "it"))))
    = do opts <- get ROpts
         case evalResultName opts of
              Nothing => throw (UndefinedName fc (UN $ Basic "it"))
              Just n => process (Check (PRef fc n))
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => undefinedName fc fn
              ts => do tys <- traverse (displayType False defs) ts
                       pure (Printed $ vsep $ map (reAnnotate Syntax) tys)
process (Check itm)
    = do (tm `WithType` ty) <- inferAndElab InExpr itm Env.empty
         defs <- get Ctxt
         itm <- resugar Env.empty !(normaliseHoles defs Env.empty tm)
         -- ty <- getTerm gty
         ity <- resugar Env.empty !(normalise defs Env.empty ty)
         pure (TermChecked itm ity)
process (CheckWithImplicits itm)
    = do showImplicits <- showImplicits <$> getPPrint
         setOpt (ShowImplicits True)
         result <- process (Check itm)
         setOpt (ShowImplicits showImplicits)
         pure result
process (PrintDef (PRef fc fn))
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => undefinedName fc fn
              ts => do defs <- traverse (displayPats False defs) ts
                       pure (Printed $ vsep $ map (reAnnotate Syntax) defs)
process (PrintDef t)
    = case !(getDocsForImplementation t) of
        Just d => pure (Printed $ reAnnotate Syntax d)
        Nothing => pure (Printed $ pretty0 "Error: could not find definition of \{show t}")
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => pure NoFileLoaded
              Just f => loadMainFile f
process (Load f)
    = do update ROpts { mainfile := Just f }
         -- Clear the context and load again
         loadMainFile f
process (ImportMod m)
    = do catch (do addImport (MkImport emptyFC False m (miAsNamespace m))
                   pure $ ModuleLoaded (show m))
               (\err => pure $ ErrorLoadingModule (show m) err)
process (CD dir)
    = do setWorkingDir dir
         workDir <- getWorkingDir
         pure (CurrentDirectory workDir)
process CWD
    = do workDir <- getWorkingDir
         pure (CurrentDirectory workDir)
process Edit
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => pure NoFileLoaded
              Just f =>
                do let line = maybe [] (\i => ["+" ++ show (i + 1)]) (errorLine opts)
                   coreLift_ $ system $ [editor opts, f] ++ line
                   loadMainFile f
process (Compile ctm outfile)
    = compileExp ctm outfile
process (Exec ctm)
    = execExp ctm
process (Help GenericHelp)
    = pure RequestedHelp
process (Help (DetailedHelp details))
    = pure (RequestedDetails details)
process (TypeSearch searchTerm)
    = do defs <- branch
         let curr = currentNS defs
         let ctxt = gamma defs
         rawTy <- desugar AnyExpr [] searchTerm
         bound <- piBindNames replFC [] rawTy
         (ty, _) <- elabTerm 0 InType [] (MkNested []) Env.empty bound Nothing
         ty' <- toResolvedNames ty
         filteredDefs <-
           do names   <- allNames ctxt
              defs    <- traverse (flip lookupCtxtExact ctxt) names
              let defs = flip mapMaybe defs $ \ md =>
                             do d <- md
                                guard (visibleIn curr (fullname d) (collapseDefault $ visibility d))
                                guard (isJust $ userNameRoot (fullname d))
                                pure d
              allDefs <- traverse (resolved ctxt) defs
              filterM (\def => equivTypes def.type ty') allDefs
         put Ctxt defs
         doc <- traverse (docsOrSignature replFC) $ fullname <$> filteredDefs
         pure $ PrintedDoc $ vsep doc
process (Missing n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName replFC n
              ts => map Missed $ traverse (\fn =>
                                         do tot <- getTotality replFC fn
                                            case isCovering tot of
                                                 MissingCases cs =>
                                                    do tms <- traverse (displayPatTerm defs) cs
                                                       pure $ CasesMissing fn tms
                                                 NonCoveringCall ns_in =>
                                                   do ns <- traverse getFullName ns_in
                                                      pure $ CallsNonCovering fn ns
                                                 _ => pure $ AllCasesCovered fn)
                               (map fst ts)
process (Total n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName replFC n
              ts => map CheckedTotal $
                    traverse (\fn =>
                          do ignore $ checkTotal replFC fn
                             tot <- getTotality replFC fn >>= toFullNames
                             pure $ (fn, tot))
                               (map fst ts)
process (Doc dir)
    = do doc <- getDocs dir
         pure $ PrintedDoc doc
process (Browse ns)
    = do doc <- getContents ns
         pure $ PrintedDoc doc
process (DebugInfo n)
    = do defs <- get Ctxt
         ds <- traverse prettyInfo !(lookupCtxtName n (gamma defs))
         pure $ PrintedDoc $ vcat $ punctuate hardline ds
process (SetOpt opt)
    = do setOpt opt
         pure Done
process GetOpts
    = do opts <- getOptions
         pure $ OptionsSet opts
process (SetLog lvl)
    = do addLogLevel lvl
         pure $ LogLevelSet lvl
process (SetConsoleWidth n)
    = do setConsoleWidth n
         pure $ ConsoleWidthSet n
process (SetColor b)
    = do setColor b
         pure $ ColorSet b
process Metavars
    = do hs <- getUserHolesData
         pure $ Printed $ reAnnotate Syntax $ prettyHoles hs

process (Editing cmd)
    = do ppopts <- getPPrint
         -- Since we're working in a local environment, don't do the usual
         -- thing of printing out the full environment for parameterised
         -- calls or calls in where blocks
         setPPrint ({ showFullEnv := False } ppopts)
         res <- processEdit cmd
         setPPrint ppopts
         pure $ Edited res
process (CGDirective str)
    = do setSession ({ directives $= (str::) } !getSession)
         pure Done
process (RunShellCommand cmd)
    = do coreLift_ (system cmd)
         pure Done
process Quit
    = pure Exited
process NOP
    = pure Done
process ShowVersion
    = pure $ VersionIs  version
process (ImportPackage package) = do
  defs <- get Ctxt
  searchDirs <- extraSearchDirectories
  let Just packageDir = find
        (\d => isInfixOf package (fromMaybe d $ fileName =<< parent d))
        searchDirs
    | _ => pure (REPLError "Package not found in the known search directories")
  let packageDirPath = parse packageDir
  tree <- coreLift $ explore packageDirPath
  fentries <- coreLift $ toPaths (toRelative tree)
  errs <- for fentries $ \entry => do
    let entry' = dropExtensions entry
    let sp = forget $ split (== dirSeparator) entry'
    let ns = concat $ intersperse "." sp
    let ns' = mkNamespace ns
    catch (do addImport (MkImport emptyFC False (nsAsModuleIdent ns') ns'); pure Nothing)
          (\err => pure (Just err))
  let errs' = catMaybes errs
  res <- case errs' of
    [] => pure "Done"
    onePlus => pure $ vsep !(traverse display onePlus)
  pure (Printed res)
 where
  toPaths : {root : _} -> Tree root -> IO (List String)
  toPaths tree =
    depthFirst (\x => map (toFilePath x ::) . force) tree (pure [])

process (FuzzyTypeSearch expr) = fuzzySearch expr

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               {auto o : Ref ROpts REPLOpts} ->
               REPLCmd -> Core REPLResult
processCatch cmd
    = do c' <- branch
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (do r <- process cmd
                   commit
                   pure r)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           msg <- display err
                           pure $ REPLError msg
                           )

parseEmptyCmd : EmptyRule (Maybe REPLCmd)
parseEmptyCmd = eoi *> (pure Nothing)

parseCmd : EmptyRule (Maybe REPLCmd)
parseCmd = do c <- command; eoi; pure $ Just c

export
parseRepl : String -> Either Error (Maybe REPLCmd)
parseRepl inp
    = case runParser (Virtual Interactive) Nothing inp (parseEmptyCmd <|> parseCmd) of
        Left err => Left err
        Right (_, _, result) => Right result

export
interpret : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            String -> Core REPLResult
interpret inp
    = do setCurrentElabSource inp
         case parseRepl inp of
           Left err => pure $ REPLError !(perror err)
           Right Nothing => pure Done
           Right (Just cmd) => processCatch cmd

mutual
  export
  replCmd : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            String -> Core ()
  replCmd "" = pure ()
  replCmd cmd
      = do res <- interpret cmd
           displayResult res

  export
  repl : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto m : Ref MD Metadata} ->
         {auto o : Ref ROpts REPLOpts} ->
         Core ()
  repl
      = do ns <- getNS
           opts <- get ROpts
           coreLift_ (putStr (prompt (evalMode opts) ++ show ns ++ "> "))
           coreLift_ (fflush stdout)
           inp <- coreLift getLine
           end <- coreLift $ fEOF stdin
           if end
             then do
               -- start a new line in REPL mode (not relevant in IDE mode)
               coreLift_ $ putStrLn ""
               iputStrLn "Bye for now!"
              else do res <- interpret inp
                      handleResult res

    where
      prompt : REPLEval -> String
      prompt EvalTC = "[tc] "
      prompt NormaliseAll = ""
      prompt Execute = "[exec] "
      prompt Scheme = "[scheme] "

  export
  handleMissing' : MissedResult -> String
  handleMissing' (CasesMissing x xs) = show x ++ ":\n" ++ showSep "\n" xs
  handleMissing' (CallsNonCovering fn ns) = (show fn ++ ": Calls non covering function"
                                           ++ (case ns of
                                                 [f] => " " ++ show f
                                                 _ => "s: " ++ showSep ", " (map show ns)))
  handleMissing' (AllCasesCovered fn) = show fn ++ ": All cases covered"

  export
  handleMissing : MissedResult -> Doc IdrisAnn
  handleMissing (CasesMissing x xs) = pretty0 x <+> colon <++> vsep (code . pretty0 <$> xs)
  handleMissing (CallsNonCovering fn ns) =
    pretty0 fn <+> colon <++> reflow "Calls non covering"
      <++> (case ns of
                 [f] => "function" <++> code (pretty0 f)
                 _ => "functions:" <++> concatWith (surround (comma <+> space)) (code . pretty0 <$> ns))
  handleMissing (AllCasesCovered fn) = pretty0 fn <+> colon <++> reflow "All cases covered"

  export
  handleResult : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto m : Ref MD Metadata} ->
         {auto o : Ref ROpts REPLOpts} -> REPLResult -> Core ()
  handleResult Exited = iputStrLn (reflow "Bye for now!")
  handleResult other = do { displayResult other ; repl }

  fileLoadingError : (fname : String) -> (err : FileError) -> (suggestion : Maybe (Doc IdrisAnn)) -> Doc IdrisAnn
  fileLoadingError fname err suggestion =
    let suggestion = maybe "" (hardline <+>) suggestion
    in
    hardline <+>
    (indent 2 $
      error ((reflow "Error loading file") <++> (dquotes $ pretty0 fname) <+> colon) <++>
        pretty0 (show err) <+>
      suggestion) <+>
    hardline

  export
  displayResult : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto o : Ref ROpts REPLOpts} -> REPLResult -> Core ()
  displayResult (REPLError err) = printResult err
  displayResult (Evaluated x Nothing) = printResult $ prettyBy Syntax x
  displayResult (Evaluated x (Just y)) = printResult (prettyBy Syntax x <++> colon <++> prettyBy Syntax y)
  displayResult (Printed xs) = printResult xs
  displayResult (PrintedDoc xs) = printDocResult xs
  displayResult (TermChecked x y) = printResult (prettyBy Syntax x <++> colon <++> prettyBy Syntax y)
  displayResult (FileLoaded x) = printResult (reflow "Loaded file" <++> pretty0 x)
  displayResult (ModuleLoaded x) = printResult (reflow "Imported module" <++> pretty0 x)
  displayResult (ErrorLoadingModule x err)
    = printResult (reflow "Error loading module" <++> pretty0 x <+> colon <++> !(perror err))
  displayResult (ErrorLoadingFile x err)
    = printResult (fileLoadingError x err Nothing)
  displayResult (ErrorsBuildingFile x errs)
    = printResult (reflow "Error(s) building file" <++> pretty0 x) -- messages already displayed while building
  displayResult NoFileLoaded = printResult (reflow "No file can be reloaded")
  displayResult (CurrentDirectory dir)
    = printResult (reflow "Current working directory is" <++> dquotes (pretty0 dir))
  displayResult CompilationFailed = printResult (reflow "Compilation failed")
  displayResult (Compiled f) = printResult ("File" <++> pretty0 f <++> "written")
  displayResult (ProofFound x) = printResult (prettyBy Syntax x)
  displayResult (Missed cases) = printResult $ vsep (handleMissing <$> cases)
  displayResult (CheckedTotal xs)
    = printResult (vsep (map (\(fn, tot) => pretty0 fn <++> "is" <++> pretty0 tot) xs))
  displayResult (LogLevelSet Nothing) = printResult (reflow "Logging turned off")
  displayResult (LogLevelSet (Just k)) = printResult (reflow "Set log level to" <++> byShow k)
  displayResult (ConsoleWidthSet (Just k)) = printResult (reflow "Set consolewidth to" <++> byShow k)
  displayResult (ConsoleWidthSet Nothing) = printResult (reflow "Set consolewidth to auto")
  displayResult (ColorSet b) = printResult (reflow (if b then "Set color on" else "Set color off"))
  displayResult (VersionIs x) = printResult (pretty0 (showVersion True x))
  displayResult (RequestedHelp) = printResult (pretty0 displayHelp)
  displayResult (RequestedDetails details) = printResult (pretty0 details)
  displayResult (Edited (DisplayEdit Empty)) = pure ()
  displayResult (Edited (DisplayEdit xs)) = printResult xs
  displayResult (Edited (EditError x)) = printResult x
  displayResult (Edited (MadeLemma lit name pty pappstr))
    = printResult $ pretty0 (relit lit (show name ++ " : " ++ show pty ++ "\n") ++ pappstr)
  displayResult (Edited (MadeWith lit wapp)) = printResult $ pretty0 $ showSep "\n" (map (relit lit) wapp)
  displayResult (Edited (MadeCase lit cstr)) = printResult $ pretty0 $ showSep "\n" (map (relit lit) cstr)
  displayResult (Edited (MadeIntro is)) = printResult $ pretty0 $ showSep "\n" (toList is)
  displayResult (OptionsSet opts) = printResult (vsep (pretty0 <$> opts))

  -- do not use a catchall so that we are warned when a new constructor is added
  displayResult Done = pure ()
  displayResult (Executed _) = pure ()
  displayResult DefDeclared = pure ()
  displayResult Exited = pure ()

  export
  displayHelp : String
  displayHelp =
    showSep "\n" $ map cmdInfo help
    where
      makeSpace : Nat -> String
      makeSpace n = pack $ take n (repeat ' ')

      col : Nat -> Nat -> String -> String -> String -> String
      col c1 c2 l m r =
        l ++ (makeSpace $ c1 `minus` length l) ++
        m ++ (makeSpace $ c2 `minus` length m) ++ r

      cmdInfo : (List String, CmdArg, String) -> String
      cmdInfo (cmds, args, text) = " " ++ col 18 36 (showSep " " cmds) (show args) text

  ||| Display errors that may occur when starting the REPL.
  ||| Does not force the REPL to exit, just prints the error(s).
  |||
  ||| NOTE: functionally the only reason to consider this function specialized
  ||| to "startup" is that it will provide suggestions to the user under the
  ||| assumption that the user has just entered the REPL via CLI arguments that
  ||| they may have used incorrectly.
  export
  displayStartupErrors : {auto o : Ref ROpts REPLOpts} ->
                         REPLResult -> Core ()
  displayStartupErrors (ErrorLoadingFile x err) =
    let suggestion = nearMatchOptSuggestion x
     in printError (fileLoadingError x err suggestion)
  displayStartupErrors _ = pure ()
