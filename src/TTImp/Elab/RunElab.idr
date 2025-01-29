module TTImp.Elab.RunElab

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import Idris.Resugar
import Idris.REPL.Opts
import Idris.Syntax

import Libraries.Data.NameMap
import Libraries.Data.WithDefault
import Libraries.Utils.Path

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Reflect
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Unelab

import System.File.Meta

import Data.SnocList

%default covering

record NameInfo where
  constructor MkNameInfo
  nametype : NameType

lookupNameInfo : Name -> Context -> Core (List (Name, NameInfo))
lookupNameInfo n ctxt
    = do res <- lookupCtxtName n ctxt
         pure (map (\ (n, i, gd) =>
                      (n, MkNameInfo { nametype = getNameType (definition gd) } ))
                   res)
  where
    getNameType : Def -> NameType
    getNameType (DCon t a _) = DataCon t a
    getNameType (TCon t a _ _ _ _ _ _) = TyCon t a
    getNameType _ = Func

Reflect NameInfo where
  reflect fc defs lhs env inf
      = do nt <- reflect fc defs lhs env (nametype inf)
           appCon fc defs (reflectiontt "MkNameInfo") [nt]

deepRefersTo : {auto c : Ref Ctxt Defs} ->
               GlobalDef -> Core (List Name)
deepRefersTo def = do
  defs <- get Ctxt
  map nub $ clos empty defs $ refs' defs def
  -- we don't start with `[defs.fullname]` to distinguish between recursive and non-recursive definitions
  where
    refs' : Defs -> GlobalDef -> List Name
    refs' defs def = keys (refersTo def)

    refs : Defs -> Name -> Core (List Name)
    refs defs n = maybe [] (refs' defs) <$> lookupCtxtExact n (gamma defs)

    clos : NameMap () -> Defs -> List Name -> Core (List Name)
    clos all _    []      = pure (keys all)
    clos all defs (n::ns) = case lookup n all of
      Just _  => clos all defs ns
      Nothing => do
        let all' = insert n () all
        let ns' = !(refs defs n) ++ ns
        clos all' defs ns'

export
elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             RigCount -> FC -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (NF vars)
elabScript rig fc nest env script@(NDCon nfc nm t ar args) exp
    = do defs <- get Ctxt
         fnm <- toFullNames nm
         case fnm of
              NS ns (UN (Basic n))
                 => if ns == reflectionNS
                      then elabCon defs n (map snd args)
                             `catch` \case -- wrap into `RunElabFail` any non-elab error
                               e@(BadRunElab _ _ _ _) => throw e
                               e@(RunElabFail _)      => throw e
                               e                      => throw $ RunElabFail e
                      else failWith defs $ "bad reflection namespace " ++ show ns
              _ => failWith defs $ "bad fullnames " ++ show fnm
  where
    failWith : Defs -> String -> Core a
    failWith defs desc
      = do empty <- clearDefs defs
           throw (BadRunElab fc env !(quote empty env script) desc)

    scriptRet : Reflect a => a -> Core (NF vars)
    scriptRet tm
        = do defs <- get Ctxt
             nfOpts withAll defs env !(reflect fc defs False env tm)

    reifyFC : Defs -> Closure vars -> Core FC
    reifyFC defs mbfc = pure $ case !(evalClosure defs mbfc >>= reify defs) of
      EmptyFC => fc
      x       => x

    -- parses and resolves `Language.Reflection.LookupDir`
    lookupDir : Defs -> NF vars -> Core String
    lookupDir defs (NDCon _ conName _ _ [<])
        = do defs <- get Ctxt
             NS ns (UN (Basic n)) <- toFullNames conName
               | fnm => failWith defs $ "bad lookup dir fullnames " ++ show fnm
             let True = ns == reflectionNS
               | False => failWith defs $ "bad lookup dir namespace " ++ show ns
             let wd = defs.options.dirs.working_dir
             let sd = maybe wd (\sd => joinPath [wd, sd]) defs.options.dirs.source_dir
             let modDir : Bool -> Core String := \doParent => do
                            syn <- get Syn
                            let parentIfNeeded = if doParent then parent else pure
                            let moduleSuffix = toList $ (head' syn.saveMod >>= parentIfNeeded) <&> toPath
                            pure $ joinPath $ sd :: moduleSuffix
             case n of
               "ProjectDir"       => pure wd
               "SourceDir"        => pure sd
               "CurrentModuleDir" => modDir True
               "SubmodulesDir"    => modDir False
               "BuildDir"         => pure $ joinPath [wd, defs.options.dirs.build_dir]
               _ => failWith defs $ "bad lookup dir value"
    lookupDir defs lk
        = do defs <- get Ctxt
             empty <- clearDefs defs
             throw (BadRunElab fc env !(quote empty env lk) "lookup dir is not a data value")

    validatePath : Defs -> String -> Core ()
    validatePath defs path = do
      let True = isRelative path
        | False => failWith defs $ "path must be relative"
      let True = pathDoesNotEscape 0 $ splitPath path
        | False => failWith defs $ "path must not escape the directory"
      pure ()
      where
        pathDoesNotEscape : (depth : Nat) -> List String -> Bool
        pathDoesNotEscape _     []           = True
        pathDoesNotEscape Z     (".."::rest) = False
        pathDoesNotEscape (S n) (".."::rest) = pathDoesNotEscape n rest
        pathDoesNotEscape n     ("." ::rest) = pathDoesNotEscape n rest
        pathDoesNotEscape n     (_   ::rest) = pathDoesNotEscape (S n) rest

    elabCon : Defs -> String -> SnocList (Closure vars) -> Core (NF vars)
    elabCon defs "Pure" [<_, val]
        = do empty <- clearDefs defs
             evalClosure empty val
    elabCon defs "Map" [<_, _, fm, act]
        -- fm : A -> B
        -- elab : A
        = do act <- elabScript rig fc nest env !(evalClosure defs act) exp
             act <- quote defs env act
             fm <- evalClosure defs fm
             applyToStack defs withHoles env fm [(getLoc act, toClosure withAll env act)]
    elabCon defs "Ap" [<_, _, actF, actX]
        -- actF : Elab (A -> B)
        -- actX : Elab A
        = do actF <- elabScript rig fc nest env !(evalClosure defs actF) exp
             actX <- elabScript rig fc nest env !(evalClosure defs actX) exp
             actX <- quote defs env actX
             applyToStack defs withHoles env actF [(getLoc actX, toClosure withAll env actX)]
    elabCon defs "Bind" [<_,_,act,k]
        -- act : Elab A
        -- k : A -> Elab B
        -- 1) Run elabScript on act stripping off Elab
        -- 2) Evaluate the resulting act
        -- 3) apply k to the result of (2)
        -- 4) Run elabScript on the result stripping off Elab
        = do act <- elabScript rig fc nest env
                                !(evalClosure defs act) exp
             act <- quote defs env act
             k <- evalClosure defs k
             r <- applyToStack defs withAll env k [(getLoc act, toClosure withAll env act)]
             elabScript rig fc nest env r exp
    elabCon defs "Fail" [<_, mbfc, msg]
        = do msg' <- evalClosure defs msg
             throw $ RunElabFail $ GenericMsg !(reifyFC defs mbfc) !(reify defs msg')
    elabCon defs "Warn" [<mbfc, msg]
        = do msg' <- evalClosure defs msg
             recordWarning $ GenericWarn !(reifyFC defs mbfc) !(reify defs msg')
             scriptRet ()
    elabCon defs "Try" [<_, elab1, elab2]
        = tryUnify (do constart <- getNextEntry
                       res <- elabScript rig fc nest env !(evalClosure defs elab1) exp
                       -- We ensure that all of the constraints introduced during the elab script
                       -- have been solved. This guarantees that we do not mistakenly succeed even
                       -- though e.g. a proof search got delayed.
                       solveConstraintsAfter constart inTerm LastChance
                       pure res)
                   (elabScript rig fc nest env !(evalClosure defs elab2) exp)
    elabCon defs "LogMsg" [<topic, verb, str]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     reify defs str'
             scriptRet ()
    elabCon defs "LogTerm" [<topic, verb, str, tm]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     tm' <- evalClosure defs tm
                     pure $ !(reify defs str') ++ ": " ++
                             show (the RawImp !(reify defs tm'))
             scriptRet ()
    elabCon defs "LogSugaredTerm" [<topic, verb, str, tm]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     tm' <- reify defs !(evalClosure defs tm)
                     ptm <- pterm (map defaultKindedName tm')
                     pure $ !(reify defs str') ++ ": " ++ show ptm
             scriptRet ()
    elabCon defs "Check" [<exp, ttimp]
        = do exp' <- evalClosure defs exp
             ttimp' <- evalClosure defs ttimp
             tidx <- resolveName (UN $ Basic "[elaborator script]")
             e <- newRef EST (initEState tidx env)
             (checktm, _) <- runDelays (const True) $
                     check rig (initElabInfo InExpr) nest env !(reify defs ttimp')
                           (Just (glueBack defs env exp'))
             empty <- clearDefs defs
             nf empty env checktm
    elabCon defs "Quote" [<exp, tm]
        = do tm' <- evalClosure defs tm
             defs <- get Ctxt
             empty <- clearDefs defs
             scriptRet $ map rawName !(unelabUniqueBinders env !(quote empty env tm'))
    elabCon defs "Lambda" [<x, _, scope]
        = do empty <- clearDefs defs
             NBind bfc x (Lam fc' c p ty) sc <- evalClosure defs scope
                   | _ => failWith defs "Not a lambda"
             n <- genVarName "x"
             sc' <- sc defs (toClosure withAll env (Ref bfc Bound n))
             qsc <- quote empty env sc'
             let lamsc = refToLocal n x qsc
             qp <- quotePi p
             qty <- quote empty env ty
             let env' = env :< Lam fc' c qp qty

             runsc <- elabScript rig fc (weaken nest) env'
                                 !(nf defs env' lamsc) Nothing -- (map weaken exp)
             nf empty env (Bind bfc x (Lam fc' c qp qty) !(quote empty env' runsc))
       where
         quotePi : PiInfo (Closure vars) -> Core (PiInfo (Term vars))
         quotePi Explicit = pure Explicit
         quotePi Implicit = pure Implicit
         quotePi AutoImplicit = pure AutoImplicit
         quotePi (DefImplicit t) = failWith defs "Can't add default lambda"
    elabCon defs "Goal" [<]
        = do let Just gty = exp
                 | Nothing => nfOpts withAll defs env
                                     !(reflect fc defs False env (the (Maybe RawImp) Nothing))
             ty <- getTerm gty
             scriptRet (Just $ map rawName $ !(unelabUniqueBinders env ty))
    elabCon defs "LocalVars" [<]
        = scriptRet vars
    elabCon defs "GenSym" [<str]
        = do str' <- evalClosure defs str
             n <- genVarName !(reify defs str')
             scriptRet n
    elabCon defs "InCurrentNS" [<n]
        = do n' <- evalClosure defs n
             nsn <- inCurrentNS !(reify defs n')
             scriptRet nsn
    elabCon defs "GetType" [<n]
        = do n' <- evalClosure defs n
             res <- lookupTyName !(reify defs n') (gamma defs)
             scriptRet !(traverse unelabType res)
      where
        unelabType : (Name, Int, ClosedTerm) -> Core (Name, RawImp)
        unelabType (n, _, ty)
            = pure (n, map rawName !(unelabUniqueBinders [<] ty))
    elabCon defs "GetInfo" [<n]
        = do n' <- evalClosure defs n
             res <- lookupNameInfo !(reify defs n') (gamma defs)
             scriptRet res
    elabCon defs "GetVis" [<n]
        = do dn <- reify defs !(evalClosure defs n)
             ds <- lookupCtxtName dn (gamma defs)
             scriptRet $ map (\(n,_,d) => (n, collapseDefault $ visibility d)) ds
    elabCon defs "GetLocalType" [<n]
        = do n' <- evalClosure defs n
             n <- reify defs n'
             case defined n env of
                  Just (MkIsDefined rigb lv) =>
                       do let binder = getBinder lv env
                          let bty = binderType binder
                          scriptRet $ map rawName !(unelabUniqueBinders env bty)
                  _ => failWith defs $ show n ++ " is not a local variable"
    elabCon defs "GetCons" [<n]
        = do n' <- evalClosure defs n
             cn <- reify defs n'
             Just (TCon _ _ _ _ _ _ cons _) <-
                     lookupDefExact cn (gamma defs)
                 | _ => failWith defs $ show cn ++ " is not a type"
             scriptRet $ fromMaybe [] cons
    elabCon defs "GetReferredFns" [<n]
        = do dn <- reify defs !(evalClosure defs n)
             Just def <- lookupCtxtExact dn (gamma defs)
                 | Nothing => failWith defs $ show dn ++ " is not a definition"
             ns <- deepRefersTo def
             scriptRet ns
    elabCon defs "GetCurrentFn" [<]
        = do defs <- get Ctxt
             scriptRet defs.defsStack
    elabCon defs "Declare" [<d]
        = do d' <- evalClosure defs d
             decls <- reify defs d'
             Core.Core.SnocList.traverse_ (processDecl [] (MkNested []) [<]) decls
             scriptRet ()
    elabCon defs "ReadFile" [<lk, pth]
        = do pathPrefix <- lookupDir defs !(evalClosure defs lk)
             path <- reify defs !(evalClosure defs pth)
             validatePath defs path
             let fullPath = joinPath [pathPrefix, path]
             True <- coreLift $ exists fullPath
               | False => scriptRet $ Nothing {ty=String}
             contents <- readFile fullPath
             scriptRet $ Just contents
    elabCon defs "WriteFile" [<lk, pth, contents]
        = do pathPrefix <- lookupDir defs !(evalClosure defs lk)
             path <- reify defs !(evalClosure defs pth)
             validatePath defs path
             contents <- reify defs !(evalClosure defs contents)
             let fullPath = joinPath [pathPrefix, path]
             whenJust (parent fullPath) ensureDirectoryExists
             writeFile fullPath contents
             scriptRet ()
    elabCon defs "IdrisDir" [<lk]
        = do evalClosure defs lk >>= lookupDir defs >>= scriptRet
    elabCon defs n args = failWith defs $ "unexpected Elab constructor " ++ n ++
                                          ", or incorrect count of arguments: " ++ show (length args)
elabScript rig fc nest env script exp
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (BadRunElab fc env !(quote empty env script) "script is not a data value")

export
checkRunElab : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> (requireExtension : Bool) -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRunElab rig elabinfo nest env fc reqExt script exp
    = do expected <- mkExpected exp
         defs <- get Ctxt
         unless (not reqExt || isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         let n = NS reflectionNS (UN $ Basic "Elab")
         elabtt <- appCon fc defs n [expected]
         (stm, sty) <- runDelays (const True) $
                           check rig elabinfo nest env script (Just (gnf env elabtt))
         solveConstraints inTerm Normal
         defs <- get Ctxt -- checking might have resolved some holes
         ntm <- elabScript rig fc nest env
                           !(nfOpts withAll defs env stm) (Just (gnf env expected))
         defs <- get Ctxt -- might have updated as part of the script
         empty <- clearDefs defs
         pure (!(quote empty env ntm), gnf env expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Term vars)
    mkExpected (Just ty) = pure !(getTerm ty)
    mkExpected Nothing
        = do nm <- genName "scriptTy"
             u <- uniVar fc
             metaVar fc erased env nm (TType fc u)
