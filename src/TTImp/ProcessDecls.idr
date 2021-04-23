module TTImp.ProcessDecls

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Termination
import Core.UnifyState

import Parser.Source

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.Parser
import TTImp.ProcessBuiltin
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessParams
import TTImp.ProcessRecord
import TTImp.ProcessRunElab
import TTImp.ProcessTransform
import TTImp.ProcessType
import TTImp.TTImp

import Data.List
import Data.Maybe
import Libraries.Data.NameMap

%default covering

-- Implements processDecl, declared in TTImp.Elab.Check
process : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          List ElabOpt ->
          NestedNames vars -> Env Term vars -> ImpDecl -> Core ()
process eopts nest env (IClaim fc rig vis opts ty)
    = processType eopts nest env fc rig vis opts ty
process eopts nest env (IData fc vis ddef)
    = processData eopts nest env fc vis ddef
process eopts nest env (IDef fc fname def)
    = processDef eopts nest env fc fname def
process eopts nest env (IParameters fc ps decls)
    = processParams nest env fc ps decls
process eopts nest env (IRecord fc ns vis rec)
    = processRecord eopts nest env ns vis rec
process eopts nest env (INamespace fc ns decls)
    = do defs <- get Ctxt
         let cns = currentNS defs
         extendNS ns
         traverse_ (processDecl eopts nest env) decls
         defs <- get Ctxt
         put Ctxt (record { currentNS = cns } defs)
process eopts nest env (ITransform fc n lhs rhs)
    = processTransform eopts nest env fc n lhs rhs
process eopts nest env (IRunElabDecl fc tm)
    = processRunElab eopts nest env fc tm
process eopts nest env (IPragma _ act)
    = act nest env
process eopts nest env (ILog lvl)
    = addLogLevel (uncurry unsafeMkLogLevel <$> lvl)
process eopts nest env (IBuiltin fc type name)
    = processBuiltin nest env fc type name

TTImp.Elab.Check.processDecl = process

export
checkTotalityOK : {auto c : Ref Ctxt Defs} ->
                  Name -> Core (Maybe Error)
checkTotalityOK (NS _ (MN _ _)) = pure Nothing -- not interested in generated names
checkTotalityOK (NS _ (CaseBlock _ _)) = pure Nothing -- case blocks checked elsewhere
checkTotalityOK n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure Nothing
         let fc = location gdef

         -- #524: need to check positivity even if we're not in a total context
         -- because a definition coming later may need to know it is positive
         case definition gdef of
           (TCon _ _ _ _ _ _ _ _) => ignore $ checkPositive fc n
           _ => pure ()

         -- Once that is done, we build up errors if necessary
         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))
         let tot = totality gdef
         log "totality" 3 $ show n ++ " must be: " ++ show treq
         case treq of
            PartialOK => pure Nothing
            CoveringOnly => checkCovering fc (isCovering tot)
            Total => checkTotality fc
  where
    checkCovering : FC -> Covering -> Core (Maybe Error)
    checkCovering fc IsCovering = pure Nothing
    checkCovering fc cov
        = pure (Just (NotCovering fc n cov))

    checkTotality : FC -> Core (Maybe Error)
    checkTotality fc
        = do ignore $ logTime ("+++ Checking Termination " ++ show n) (checkTotal fc n)
             -- ^ checked lazily, so better calculate here
             t <- getTotality fc n
             err <- checkCovering fc (isCovering t)
             maybe (case isTerminating t of
                         NotTerminating p => pure (Just (NotTotal fc n p))
                         _ => pure Nothing)
                   (pure . Just) err

-- Check totality of all the names added in the file, and return a list of
-- totality errors.
-- Do this at the end of processing a file (or a batch of definitions) since
-- they might be mutually dependent so we need all the definitions to be able
-- to check accurately.
export
getTotalityErrors : {auto c : Ref Ctxt Defs} ->
                    Core (List Error)
getTotalityErrors
    = do defs <- get Ctxt
         errs <- traverse checkTotalityOK (keys (toSave defs))
         pure (mapMaybe id errs)

export
processDecls : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processDecls nest env decls
    = do traverse_ (processDecl [] nest env) decls
         pure True -- TODO: False on error

processTTImpDecls : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto m : Ref MD Metadata} ->
                    {auto u : Ref UST UState} ->
                    NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processTTImpDecls {vars} nest env decls
    = do traverse_ (\d => do d' <- bindNames d
                             processDecl [] nest env d') decls
         pure True -- TODO: False on error
  where
    bindConNames : ImpTy -> Core ImpTy
    bindConNames (MkImpTy fc nameFC n ty)
        = do ty' <- bindTypeNames [] vars ty
             pure (MkImpTy fc nameFC n ty')

    bindDataNames : ImpData -> Core ImpData
    bindDataNames (MkImpData fc n t opts cons)
        = do t' <- bindTypeNames [] vars t
             cons' <- traverse bindConNames cons
             pure (MkImpData fc n t' opts cons')
    bindDataNames (MkImpLater fc n t)
        = do t' <- bindTypeNames [] vars t
             pure (MkImpLater fc n t')

    -- bind implicits to make raw TTImp source a bit friendlier
    bindNames : ImpDecl -> Core ImpDecl
    bindNames (IClaim fc c vis opts (MkImpTy tfc nameFC n ty))
        = do ty' <- bindTypeNames [] vars ty
             pure (IClaim fc c vis opts (MkImpTy tfc nameFC n ty'))
    bindNames (IData fc vis d)
        = do d' <- bindDataNames d
             pure (IData fc vis d')
    bindNames d = pure d

export
processTTImpFile : {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   String -> Core Bool
processTTImpFile fname
    = do Right tti <- logTime "Parsing" $ coreLift $ parseFile fname
                            (do decls <- prog fname
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         logTime "Elaboration" $
            catch (do ignore $ processTTImpDecls (MkNested []) [] tti
                      Nothing <- checkDelayedHoles
                          | Just err => throw err
                      pure True)
                  (\err => do coreLift_ (printLn err)
                              pure False)
