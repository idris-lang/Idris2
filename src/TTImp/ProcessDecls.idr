module TTImp.ProcessDecls

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Env
import Core.Metadata
import Core.Options
import Core.Termination
import Core.UnifyState

import Idris.Error
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Syntax
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
import Data.String
import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter.Doc

%default covering

||| When we process a failing block we want to know what happend
data FailedFailure
  = DidNotFail
  | IncorrectlyFailed Error

processFailing :
  {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto m : Ref MD Metadata} ->
  {auto u : Ref UST UState} ->
  {auto s : Ref Syn SyntaxInfo} ->
  {auto o : Ref ROpts REPLOpts} ->
  List ElabOpt ->
  NestedNames vars -> Env Term vars ->
  FC -> Maybe String ->  List ImpDecl -> Core ()
processFailing eopts nest env fc mmsg decls
    = do -- save the state: the content of a failing block should be discarded
         ust <- get UST
         syn <- get Syn
         md <- get MD
         defs <- branch
         -- We're going to run the elaboration, and then return:
         -- * Nothing                      if the block correctly failed
         -- * Just DidNotFail              if it incorrectly succeeded
         -- * Just (IncorrectlyFailed err) if the block failed with the wrong error
         result <- catch
               (do -- Run the elaborator
                   traverse_ (processDecl eopts nest env) decls
                   -- We have (unfortunately) succeeded
                   pure (Just $ FailingDidNotFail fc))
               (\err => do let Just msg = mmsg
                                 | _ => pure Nothing
                           log "elab.failing" 10 $ "Failing block based on \{show msg} failed with \{show err}"
                           test <- checkError msg err
                           pure $ do -- Unless the error is the expected one
                                     guard (not test)
                                     -- We should complain we had the wrong one
                                     pure (FailingWrongError fc msg err))
         md' <- get MD
         -- Reset the state
         put UST ust
         put Syn syn
         -- For metadata, we preserve the syntax highlithing information (but none
         -- of the things that may include code that's dropped like types, LHSs, etc.)
         put MD ({ semanticHighlighting := semanticHighlighting md'
                 , semanticAliases := semanticAliases md'
                 , semanticDefaults := semanticDefaults md'
                 } md)
         put Ctxt defs
         -- And fail if the block was successfully accepted
         whenJust result throw


-- Implements processDecl, declared in TTImp.Elab.Check
process : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          List ElabOpt ->
          NestedNames vars -> Env Term vars -> ImpDecl -> Core ()
process eopts nest env (IClaim fc rig vis opts ty)
    = processType eopts nest env fc rig vis opts ty
process eopts nest env (IData fc vis mbtot ddef)
    = processData eopts nest env fc vis mbtot ddef
process eopts nest env (IDef fc fname def)
    = processDef eopts nest env fc fname def
process eopts nest env (IParameters fc ps decls)
    = processParams nest env fc ps decls
process eopts nest env (IRecord fc ns vis mbtot rec)
    = processRecord eopts nest env ns vis mbtot rec
process eopts nest env (IFail fc msg decls)
    = processFailing eopts nest env fc msg decls
process eopts nest env (INamespace fc ns decls)
    = withExtendedNS ns $
         traverse_ (processDecl eopts nest env) decls
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
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processDecls nest env decls
    = do traverse_ (processDecl [] nest env) decls
         pure True -- TODO: False on error

processTTImpDecls : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto m : Ref MD Metadata} ->
                    {auto u : Ref UST UState} ->
                    {auto s : Ref Syn SyntaxInfo} ->
                    {auto o : Ref ROpts REPLOpts} ->
                    NestedNames vars -> Env Term vars -> List ImpDecl -> Core Bool
processTTImpDecls {vars} nest env decls
    = do traverse_ (\d => do d' <- bindNames d
                             processDecl [] nest env d') decls
         pure True -- TODO: False on error
  where
    bindConNames : ImpTy -> Core ImpTy
    bindConNames (MkImpTy fc nameFC n ty)
        = do ty' <- bindTypeNames fc [] vars ty
             pure (MkImpTy fc nameFC n ty')

    bindDataNames : ImpData -> Core ImpData
    bindDataNames (MkImpData fc n t opts cons)
        = do t' <- bindTypeNames fc [] vars t
             cons' <- traverse bindConNames cons
             pure (MkImpData fc n t' opts cons')
    bindDataNames (MkImpLater fc n t)
        = do t' <- bindTypeNames fc [] vars t
             pure (MkImpLater fc n t')

    -- bind implicits to make raw TTImp source a bit friendlier
    bindNames : ImpDecl -> Core ImpDecl
    bindNames (IClaim fc c vis opts (MkImpTy tfc nameFC n ty))
        = do ty' <- bindTypeNames fc [] vars ty
             pure (IClaim fc c vis opts (MkImpTy tfc nameFC n ty'))
    bindNames (IData fc vis mbtot d)
        = do d' <- bindDataNames d
             pure (IData fc vis mbtot d')
    bindNames d = pure d

export
processTTImpFile : {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   String -> Core Bool
processTTImpFile fname
    = do modIdent <- ctxtPathToNS fname
         Right (ws, decor, tti) <- logTime "Parsing" $
                            coreLift $ parseFile fname (PhysicalIdrSrc modIdent)
                            (do decls <- prog (PhysicalIdrSrc modIdent)
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         traverse_ recordWarning ws
         logTime "Elaboration" $
            catch (do ignore $ processTTImpDecls (MkNested []) [] tti
                      Nothing <- checkDelayedHoles
                          | Just err => throw err
                      pure True)
                  (\err => do coreLift_ (printLn err)
                              pure False)
