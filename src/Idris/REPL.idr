module Idris.REPL

import Compiler.Common

import Core.AutoSearch
import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Env
import Core.InitPrimitives
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Termination
import Core.TT
import Core.Unify

import Parser.Unlit

import Idris.Desugar
import Idris.DocString
import Idris.Error
import Idris.IDEMode.CaseSplit
import Idris.IDEMode.Commands
import Idris.IDEMode.MakeClause
import Idris.IDEMode.Holes
import Idris.ModTree
import Idris.Parser
import Idris.ProcessIdr
import Idris.Resugar
import public Idris.REPLCommon
import Idris.Syntax
import Idris.Version

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.CaseSplit
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Interactive.MakeLemma
import TTImp.TTImp
import TTImp.ProcessDecls

import Data.List
import Data.Maybe
import Data.NameMap
import Data.Stream
import Data.Strings

import System
import System.File

%default covering

showInfo : {auto c : Ref Ctxt Defs} ->
           (Name, Int, GlobalDef) -> Core ()
showInfo (n, idx, d)
    = do coreLift $ putStrLn (show (fullname d) ++ " ==> " ++
                              show !(toFullNames (definition d)))
         coreLift $ putStrLn (show (multiplicity d))
         coreLift $ putStrLn ("Erasable args: " ++ show (eraseArgs d))
         coreLift $ putStrLn ("Detaggable arg types: " ++ show (safeErase d))
         coreLift $ putStrLn ("Specialise args: " ++ show (specArgs d))
         coreLift $ putStrLn ("Inferrable args: " ++ show (inferrable d))
         case compexpr d of
              Nothing => pure ()
              Just expr => coreLift $ putStrLn ("Compiled: " ++ show expr)
         coreLift $ putStrLn ("Refers to: " ++
                               show !(traverse getFullName (keys (refersTo d))))
         coreLift $ putStrLn ("Refers to (runtime): " ++
                               show !(traverse getFullName (keys (refersToRuntime d))))
         coreLift $ putStrLn ("Flags: " ++ show (flags d))
         when (not (isNil (sizeChange d))) $
            let scinfo = map (\s => show (fnCall s) ++ ": " ++
                                    show (fnArgs s)) !(traverse toFullNames (sizeChange d)) in
                coreLift $ putStrLn $
                        "Size change: " ++ showSep ", " scinfo

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core String
displayType defs (n, i, gdef)
    = maybe (do tm <- resugar [] !(normaliseHoles defs [] (type gdef))
                pure (show !(aliasName (fullname gdef)) ++ " : " ++ show tm))
            (\num => showHole defs [] n num (type gdef))
            (isHole gdef)

getEnvTerm : {vars : _} ->
             List Name -> Env Term vars -> Term vars ->
             (vars' ** (Env Term vars', Term vars'))
getEnvTerm (n :: ns) env (Bind fc x b sc)
    = if n == x
         then getEnvTerm ns (b :: env) sc
         else (_ ** (env, Bind fc x b sc))
getEnvTerm _ env tm = (_ ** (env, tm))

displayTerm : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> ClosedTerm ->
              Core String
displayTerm defs tm
    = do ptm <- resugar [] !(normaliseHoles defs [] tm)
         pure (show ptm)

displayPatTerm : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Defs -> ClosedTerm ->
                 Core String
displayPatTerm defs tm
    = do ptm <- resugarNoPatvars [] !(normaliseHoles defs [] tm)
         pure (show ptm)

displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Defs -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core String
displayClause defs (vs ** (env, lhs, rhs))
    = do lhstm <- resugar env !(normaliseHoles defs env lhs)
         rhstm <- resugar env !(normaliseHoles defs env rhs)
         pure (show lhstm ++ " = " ++ show rhstm)

displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core String
displayPats defs (n, idx, gdef)
    = case definition gdef of
           PMDef _ _ _ _ pats
               => do ty <- displayType defs (n, idx, gdef)
                     ps <- traverse (displayClause defs) pats
                     pure (ty ++ "\n" ++ showSep "\n" ps)
           _ => pure (show n ++ " is not a pattern matching definition")

setOpt : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         REPLOpt -> Core ()
setOpt (ShowImplicits t)
    = do pp <- getPPrint
         setPPrint (record { showImplicits = t } pp)
setOpt (ShowNamespace t)
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = t } pp)
setOpt (ShowTypes t)
    = do opts <- get ROpts
         put ROpts (record { showTypes = t } opts)
setOpt (EvalMode m)
    = do opts <- get ROpts
         put ROpts (record { evalMode = m } opts)
setOpt (Editor e)
    = do opts <- get ROpts
         put ROpts (record { editor = e } opts)
setOpt (CG e)
    = do defs <- get Ctxt
         case getCG (options defs) e of
            Just cg => setCG cg
            Nothing => iputStrLn "No such code generator available"

getOptions : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         Core (List REPLOpt)
getOptions = do
  pp <- getPPrint
  opts <- get ROpts
  pure $ [ ShowImplicits (showImplicits pp), ShowNamespace (fullNamespace pp)
         , ShowTypes (showTypes opts), EvalMode (evalMode opts)
         , Editor (editor opts)
         ]

export
findCG : {auto o : Ref ROpts REPLOpts} ->
         {auto c : Ref Ctxt Defs} -> Core Codegen
findCG
    = do defs <- get Ctxt
         let (MkCG s) = codegen (session (options defs))
         case !(getCodegen s) of
              Just cg => pure cg
              Nothing => do coreLift $ putStrLn ("No such code generator: " ++ s)
                            coreLift $ exitWith (ExitFailure 1)

anyAt : (FC -> Bool) -> FC -> a -> Bool
anyAt p loc y = p loc

printClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Maybe String -> Nat -> ImpClause ->
              Core String
printClause l i (PatClause _ lhsraw rhsraw)
    = do lhs <- pterm lhsraw
         rhs <- pterm rhsraw
         pure (relit l (pack (replicate i ' ') ++ show lhs ++ " = " ++ show rhs))
printClause l i (WithClause _ lhsraw wvraw flags csraw)
    = do lhs <- pterm lhsraw
         wval <- pterm wvraw
         cs <- traverse (printClause l (i + 2)) csraw
         pure ((relit l ((pack (replicate i ' ') ++ show lhs ++ " with (" ++ show wval ++ ")\n")) ++
                 showSep "\n" cs))
printClause l i (ImpossibleClause _ lhsraw)
    = do lhs <- pterm lhsraw
         pure (relit l (pack (replicate i ' ') ++ show lhs ++ " impossible"))


lookupDefTyName : Name -> Context ->
                  Core (List (Name, Int, (Def, ClosedTerm)))
lookupDefTyName = lookupNameBy (\g => (definition g, type g))

public export
data EditResult : Type where
  DisplayEdit : List String -> EditResult
  EditError : String -> EditResult
  MadeLemma : Maybe String -> Name -> PTerm -> String -> EditResult
  MadeWith : Maybe String -> List String -> EditResult
  MadeCase : Maybe String -> List String -> EditResult

updateFile : {auto r : Ref ROpts REPLOpts} ->
             (List String -> List String) -> Core EditResult
updateFile update
    = do opts <- get ROpts
         let Just f = mainfile opts
             | Nothing => pure (DisplayEdit []) -- no file, nothing to do
         Right content <- coreLift $ readFile f
               | Left err => throw (FileErr f err)
         coreLift $ writeFile (f ++ "~") content
         coreLift $ writeFile f (unlines (update (lines content)))
         pure (DisplayEdit [])

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

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core EditResult
processEdit (TypeAt line col name)
    = do defs <- get Ctxt
         glob <- lookupCtxtName name (gamma defs)
         res <- the (Core String) $ case glob of
                     [] => pure ""
                     ts => do tys <- traverse (displayType defs) ts
                              pure (showSep "\n" tys)
         Just (n, num, t) <- findTypeAt (\p, n => within (line-1, col-1) p)
            | Nothing => if res == ""
                            then throw (UndefinedName (MkFC "(interactive)" (0,0) (0,0)) name)
                            else pure (DisplayEdit [res])
         if res == ""
            then pure (DisplayEdit [ nameRoot n ++ " : " ++
                                       !(displayTerm defs t)])
            else pure (DisplayEdit [])  -- ? Why () This means there is a global name and a type at (line,col)
processEdit (CaseSplit upd line col name)
    = do let find = if col > 0
                       then within (line-1, col-1)
                       else onLine (line-1)
         OK splits <- getSplits (anyAt find) name
             | SplitFail err => pure (EditError (show err))
         lines <- updateCase splits (line-1) (col-1)
         if upd
            then updateFile (caseSplit (unlines lines) (integerToNat (cast (line - 1))))
            else pure $ DisplayEdit lines
processEdit (AddClause upd line name)
    = do Just c <- getClause line name
             | Nothing => pure (EditError (show name ++ " not defined here"))
         if upd
            then updateFile (addClause c (integerToNat (cast line)))
            else pure $ DisplayEdit [c]
processEdit (ExprSearch upd line name hints all)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefName name (gamma defs)) of
              [(n, nidx, Hole locs _)] =>
                  do tms <- exprSearch replFC name []
                     defs <- get Ctxt
                     restms <- traverse (normaliseHoles defs []) tms
                     itms <- the (Core (List PTerm))
                               (traverse (\tm =>
                                           do let (_ ** (env, tm')) = dropLams locs [] tm
                                              resugar env tm') restms)
                     if all
                        then pure $ DisplayEdit (map show itms)
                        else case itms of
                                  [] => pure $ EditError "No search results"
                                  (x :: xs) =>
                                     let res = show (the PTerm (if brack
                                                        then addBracket replFC x
                                                        else x)) in
                                       if upd
                                          then updateFile (proofSearch name res (integerToNat (cast (line - 1))))
                                          else pure $ DisplayEdit [res]
              [(n, nidx, PMDef pi [] (STerm _ tm) _ _)] =>
                  case holeInfo pi of
                       NotHole => pure $ EditError "Not a searchable hole"
                       SolvedHole locs =>
                          do let (_ ** (env, tm')) = dropLams locs [] tm
                             itm <- resugar env tm'
                             let res = show (the PTerm (if brack
                                                then addBracket replFC itm
                                                else itm))
                             if upd
                                then updateFile (proofSearch name res (integerToNat (cast (line - 1))))
                                else pure $ DisplayEdit [res]
              [] => pure $ EditError $ "Unknown name " ++ show name
              _ => pure $ EditError "Not a searchable hole"
  where
    dropLams : {vars : _} ->
               Nat -> Env Term vars -> Term vars ->
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ _ b sc) = dropLams k (b :: env) sc
    dropLams _ env tm = (_ ** (env, tm))
processEdit (GenerateDef upd line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine (line - 1) p)
             | Nothing => pure (EditError ("Can't find declaration for " ++ show name ++ " on line " ++ show line))
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do Just (fc, cs) <- makeDef (\p, n => onLine (line - 1) p) n'
                           | Nothing => processEdit (AddClause upd line name)
                        Just srcLine <- getSourceLine line
                           | Nothing => pure (EditError "Source line not found")
                        let (markM, srcLineUnlit) = isLitLine srcLine
                        let l : Nat =  integerToNat (cast (snd (startPos fc)))
                        ls <- traverse (printClause markM l) cs
                        if upd
                           then updateFile (addClause (unlines ls) (integerToNat (cast line)))
                           else pure $ DisplayEdit ls)
                    (\err => pure $ EditError $ "Can't find a definition for " ++ show n' ++ ": " ++ show err)
              Just _ => pure $ EditError "Already defined"
              Nothing => pure $ EditError $ "Can't find declaration for " ++ show name
processEdit (MakeLemma upd line name)
    = do defs <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case !(lookupDefTyName name (gamma defs)) of
              [(n, nidx, Hole locs _, ty)] =>
                  do (lty, lapp) <- makeLemma replFC name locs ty
                     pty <- pterm lty
                     papp <- pterm lapp
                     opts <- get ROpts
                     let pappstr = show (the PTerm (if brack
                                            then addBracket replFC papp
                                            else papp))
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

public export
data MissedResult : Type where
  CasesMissing : Name -> List String  -> MissedResult
  CallsNonCovering : Name -> List Name -> MissedResult
  AllCasesCovered : Name -> MissedResult

public export
data REPLResult : Type where
  Done : REPLResult
  REPLError : String -> REPLResult
  Executed : PTerm -> REPLResult
  RequestedHelp : REPLResult
  Evaluated : PTerm -> (Maybe PTerm) -> REPLResult
  Printed : List String -> REPLResult
  TermChecked : PTerm -> PTerm -> REPLResult
  FileLoaded : String -> REPLResult
  ModuleLoaded : String -> REPLResult
  ErrorLoadingModule : String -> Error -> REPLResult
  ErrorLoadingFile : String -> FileError -> REPLResult
  ErrorsBuildingFile : String -> List Error -> REPLResult
  NoFileLoaded : REPLResult
  CurrentDirectory : String -> REPLResult
  CompilationFailed: REPLResult
  Compiled : String -> REPLResult
  ProofFound : PTerm -> REPLResult
  Missed : List MissedResult -> REPLResult
  CheckedTotal : List (Name, Totality) -> REPLResult
  FoundHoles : List HoleData -> REPLResult
  OptionsSet : List REPLOpt -> REPLResult
  LogLevelSet : Nat -> REPLResult
  VersionIs : Version -> REPLResult
  DefDeclared : REPLResult
  Exited : REPLResult
  Edited : EditResult -> REPLResult

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref MD Metadata} ->
          {auto o : Ref ROpts REPLOpts} ->
          PTerm -> Core REPLResult
execExp ctm
    = do ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         inidx <- resolveName (UN "[input]")
         (tm, ty) <- elabTerm inidx InExpr [] (MkNested [])
                                 [] ttimp Nothing
         tm_erased <- linearCheck replFC linear True [] tm
         execute !findCG tm_erased
         pure $ Executed ctm


execDecls : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            List PDecl -> Core REPLResult
execDecls decls = do
  traverse_ execDecl decls
  pure DefDeclared
  where
    execDecl : PDecl -> Core ()
    execDecl decl = do
      i <- desugarDecl [] decl
      traverse_ (processDecl [] (MkNested []) []) i

export
compileExp : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto m : Ref MD Metadata} ->
             {auto o : Ref ROpts REPLOpts} ->
             PTerm -> String -> Core REPLResult
compileExp ctm outfile
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, gty) <- elabTerm inidx InExpr [] (MkNested [])
                               [] ttimp Nothing
         tm_erased <- linearCheck replFC linear True [] tm
         ok <- compile !findCG tm_erased outfile
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
    = do resetContext
         Right res <- coreLift (readFile f)
            | Left err => do setSource ""
                             pure (ErrorLoadingFile f err)
         errs <- logTime "Build deps" $ buildDeps f
         updateErrorLine errs
         setSource res
         case errs of
           [] => pure (FileLoaded f)
           _ => pure (ErrorsBuildingFile f errs)


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
         case evalMode opts of
            Execute => do execExp itm; pure (Executed itm)
            _ =>
              do ttimp <- desugar AnyExpr [] itm
                 inidx <- resolveName (UN "[input]")
                 -- a TMP HACK to prioritise list syntax for List: hide
                 -- foreign argument lists. TODO: once the new FFI is fully
                 -- up and running we won't need this. Also, if we add
                 -- 'with' disambiguation we can use that instead.
                 catch (do hide replFC (NS ["PrimIO"] (UN "::"))
                           hide replFC (NS ["PrimIO"] (UN "Nil")))
                       (\err => pure ())
                 (tm, gty) <- elabTerm inidx (emode (evalMode opts)) [] (MkNested [])
                                       [] ttimp Nothing
                 defs <- get Ctxt
                 opts <- get ROpts
                 let norm = nfun (evalMode opts)
                 ntm <- norm defs [] tm
                 itm <- resugar [] ntm
                 logTermNF 5 "Normalised" [] ntm
                 if showTypes opts
                    then do ty <- getTerm gty
                            ity <- resugar [] !(norm defs [] ty)
                            pure (Evaluated itm (Just ity))
                    else pure (Evaluated itm Nothing)
  where
    emode : REPLEval -> ElabMode
    emode EvalTC = InType
    emode _ = InExpr

    nfun : {vs : _} ->
           REPLEval -> Defs -> Env Term vs -> Term vs -> Core (Term vs)
    nfun NormaliseAll = normaliseAll
    nfun _ = normalise
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName fc fn)
              ts => do tys <- traverse (displayType defs) ts
                       pure (Printed tys)
process (Check itm)
    = do inidx <- resolveName (UN "[input]")
         ttimp <- desugar AnyExpr [] itm
         (tm, gty) <- elabTerm inidx InExpr [] (MkNested [])
                                  [] ttimp Nothing
         defs <- get Ctxt
         itm <- resugar [] !(normaliseHoles defs [] tm)
         ty <- getTerm gty
         ity <- resugar [] !(normaliseScope defs [] ty)
         pure (TermChecked itm ity)
process (PrintDef fn)
    = do defs <- get Ctxt
         case !(lookupCtxtName fn (gamma defs)) of
              [] => throw (UndefinedName replFC fn)
              ts => do defs <- traverse (displayPats defs) ts
                       pure (Printed defs)
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => pure NoFileLoaded
              Just f => loadMainFile f
process (Load f)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just f } opts)
         -- Clear the context and load again
         loadMainFile f
process (ImportMod m)
    = do catch (do addImport (MkImport emptyFC False m m)
                   pure $ ModuleLoaded (showSep "." (reverse m)))
               (\err => pure $ ErrorLoadingModule (showSep "." (reverse m)) err)
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
                do let line = maybe "" (\i => " +" ++ show (i + 1)) (errorLine opts)
                   coreLift $ system (editor opts ++ " " ++ f ++ line)
                   loadMainFile f
process (Compile ctm outfile)
    = compileExp ctm outfile
process (Exec ctm)
    = execExp ctm
process Help
    = pure RequestedHelp
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | [] => throw (UndefinedName replFC n_in)
              | ns => throw (AmbiguousName replFC (map fst ns))
         tm <- search replFC top False 1000 n ty []
         itm <- resugar [] !(normaliseHoles defs [] tm)
         pure $ ProofFound itm
process (Missing n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => throw (UndefinedName replFC n)
              ts => map Missed $ traverse (\fn =>
                                         do tot <- getTotality replFC fn
                                            the (Core MissedResult) $ case isCovering tot of
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
              [] => throw (UndefinedName replFC n)
              ts => map CheckedTotal $
                    traverse (\fn =>
                          do checkTotal replFC fn
                             tot <- getTotality replFC fn >>= toFullNames
                             pure $ (fn, tot))
                               (map fst ts)
process (Doc n)
    = do doc <- getDocsFor replFC n
         pure $ Printed doc
process (Browse ns)
    = do doc <- getContents ns
         pure $ Printed doc
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure Done
process (SetOpt opt)
    = do setOpt opt
         pure Done
process GetOpts
    = do opts <- getOptions
         pure $ OptionsSet opts
process (SetLog lvl)
    = do setLogLevel lvl
         pure $ LogLevelSet lvl
process Metavars
    = do defs <- get Ctxt
         let ctxt = gamma defs
         ms  <- getUserHoles
         let globs = concat !(traverse (\n => lookupCtxtName n ctxt) ms)
         let holesWithArgs = mapMaybe (\(n, i, gdef) => do args <- isHole gdef
                                                           pure (n, gdef, args))
                                      globs
         hData <- the (Core $ List HoleData) $
             traverse (\n_gdef_args =>
                        -- Inference can't deal with this for now :/
                        let (n, gdef, args) = the (Name, GlobalDef, Nat) n_gdef_args in
                        holeData defs [] n args (type gdef))
                      holesWithArgs
         pure $ FoundHoles hData

process (Editing cmd)
    = do ppopts <- getPPrint
         -- Since we're working in a local environment, don't do the usual
         -- thing of printing out the full environment for parameterised
         -- calls or calls in where blocks
         setPPrint (record { showFullEnv = False } ppopts)
         res <- processEdit cmd
         setPPrint ppopts
         pure $ Edited res
process Quit
    = pure Exited
process NOP
    = pure Done
process ShowVersion
    = pure $ VersionIs  version

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
         catch (do ust <- get UST
                   r <- process cmd
                   commit
                   pure r)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           pure $ REPLError !(display err)
                           )

parseEmptyCmd : SourceEmptyRule (Maybe REPLCmd)
parseEmptyCmd = eoi *> (pure Nothing)

parseCmd : SourceEmptyRule (Maybe REPLCmd)
parseCmd = do c <- command; eoi; pure $ Just c

export
parseRepl : String -> Either (ParseError Token) (Maybe REPLCmd)
parseRepl inp
    = case fnameCmd [(":load ", Load), (":l ", Load), (":cd ", CD)] inp of
           Nothing => runParser Nothing inp (parseEmptyCmd <|> parseCmd)
           Just cmd => Right $ Just cmd
  where
    -- a right load of hackery - we can't tokenise the filename using the
    -- ordinary parser. There's probably a better way...
    getLoad : Nat -> (String -> REPLCmd) -> String -> Maybe REPLCmd
    getLoad n cmd str = Just (cmd (trim (substr n (length str) str)))

    fnameCmd : List (String, String -> REPLCmd) -> String -> Maybe REPLCmd
    fnameCmd [] inp = Nothing
    fnameCmd ((pre, cmd) :: rest) inp
        = if isPrefixOf pre inp
             then getLoad (length pre) cmd inp
             else fnameCmd rest inp

export
interpret : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            String -> Core REPLResult
interpret inp
    = case parseRepl inp of
           Left err => pure $ REPLError (show err)
           Right Nothing => pure Done
           Right (Just cmd) => do
             setCurrentElabSource inp
             processCatch cmd

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
           coreLift (putStr (prompt (evalMode opts) ++ showSep "." (reverse ns) ++ "> "))
           inp <- coreLift getLine
           end <- coreLift $ fEOF stdin
           if end
             then do
               -- start a new line in REPL mode (not relevant in IDE mode)
               coreLift $ putStrLn ""
               iputStrLn "Bye for now!"
              else do res <- interpret inp
                      handleResult res

    where
      prompt : REPLEval -> String
      prompt EvalTC = "[tc] "
      prompt NormaliseAll = ""
      prompt Execute = "[exec] "

  export
  handleMissing : MissedResult -> String
  handleMissing (CasesMissing x xs) = show x ++ ":\n" ++ showSep "\n" xs
  handleMissing (CallsNonCovering fn ns) = (show fn ++ ": Calls non covering function"
                                           ++ (case ns of
                                                 [f] => " " ++ show f
                                                 _ => "s: " ++ showSep ", " (map show ns)))
  handleMissing (AllCasesCovered fn) = show fn ++ ": All cases covered"

  export
  handleResult : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto m : Ref MD Metadata} ->
         {auto o : Ref ROpts REPLOpts} -> REPLResult -> Core ()
  handleResult Exited = iputStrLn "Bye for now!"
  handleResult other = do { displayResult other ; repl }

  export
  displayResult : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto m : Ref MD Metadata} ->
         {auto o : Ref ROpts REPLOpts} -> REPLResult -> Core ()
  displayResult  (REPLError err) = printError err
  displayResult  (Evaluated x Nothing) = printResult $ show x
  displayResult  (Evaluated x (Just y)) = printResult $ show x ++ " : " ++ show y
  displayResult  (Printed xs) = printResult (showSep "\n" xs)
  displayResult  (TermChecked x y) = printResult $ show x ++ " : " ++ show y
  displayResult  (FileLoaded x) = printResult $ "Loaded file " ++ x
  displayResult  (ModuleLoaded x) = printResult $ "Imported module " ++ x
  displayResult  (ErrorLoadingModule x err) = printError $ "Error loading module " ++ x ++ ": " ++ !(perror err)
  displayResult  (ErrorLoadingFile x err) = printError $ "Error loading file " ++ x ++ ": " ++ show err
  displayResult  (ErrorsBuildingFile x errs) = printError $ "Error(s) building file " ++ x -- messages already displayed while building
  displayResult  NoFileLoaded = printError "No file can be reloaded"
  displayResult  (CurrentDirectory dir) = printResult ("Current working directory is '" ++ dir ++ "'")
  displayResult  CompilationFailed = printError "Compilation failed"
  displayResult  (Compiled f) = printResult $ "File " ++ f ++ " written"
  displayResult  (ProofFound x) = printResult $ show x
  displayResult  (Missed cases) = printResult $ showSep "\n" $ map handleMissing cases
  displayResult  (CheckedTotal xs) = printResult $ showSep "\n" $ map (\ (fn, tot) => (show fn ++ " is " ++ show tot)) xs
  displayResult  (FoundHoles []) = printResult $ "No holes"
  displayResult  (FoundHoles [x]) = printResult $ "1 hole: " ++ show x.name
  displayResult  (FoundHoles xs) = printResult $ show (length xs) ++ " holes: " ++
                                   showSep ", " (map (show . name) xs)
  displayResult  (LogLevelSet k) = printResult $ "Set loglevel to " ++ show k
  displayResult  (VersionIs x) = printResult $ showVersion True x
  displayResult  (RequestedHelp) = printResult displayHelp
  displayResult  (Edited (DisplayEdit [])) = pure ()
  displayResult  (Edited (DisplayEdit xs)) = printResult $ showSep "\n" xs
  displayResult  (Edited (EditError x)) = printError x
  displayResult  (Edited (MadeLemma lit name pty pappstr)) = printResult (relit lit (show name ++ " : " ++ show pty ++ "\n") ++ pappstr)
  displayResult  (Edited (MadeWith lit wapp)) = printResult $ showSep "\n" (map (relit lit) wapp)
  displayResult  (Edited (MadeCase lit cstr)) = printResult $ showSep "\n" (map (relit lit) cstr)
  displayResult  (OptionsSet opts) = printResult $ showSep "\n" $ map show opts
  displayResult  _ = pure ()

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
      cmdInfo (cmds, args, text) = " " ++ col 16 12 (showSep " " cmds) (show args) text

  export
  displayErrors : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         {auto s : Ref Syn SyntaxInfo} ->
         {auto m : Ref MD Metadata} ->
         {auto o : Ref ROpts REPLOpts} -> REPLResult -> Core ()
  displayErrors  (ErrorLoadingFile x err) = printError $ "File error in " ++ x ++ ": " ++ show err
  displayErrors _ = pure ()
