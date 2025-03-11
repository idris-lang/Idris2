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

import TTImp.ProcessDecls.Totality

import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter.Doc

%default covering

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

         -- We expect the block to fail and so the definitions introduced
         -- in it should be discarded once we leave the block.
         defs <- branch

         -- We're going to run the elaboration, and then return:
         -- * Nothing     if the block correctly failed
         -- * Just err    if it either did not fail or failed with an invalid error message
         result <- catch
               (do -- Run the elaborator
                   before <- getTotalityErrors
                   traverse_ (processDecl eopts nest env) decls
                   after <- getTotalityErrors
                   let errs = after \\ before
                   let (e :: es) = errs
                     | [] => do -- We better have unsolved holes
                                -- checkUserHoles True -- do we need this one too?

                                 -- should we only look at the ones introduced in the block?
                                Nothing <- checkDelayedHoles
                                  | Just err => throw err

                                -- Or we have (unfortunately) succeeded
                                pure (Just $ FailingDidNotFail fc)
                   let Just msg = mmsg
                     | _ => pure Nothing
                   log "elab.failing" 10 $ "Failing block based on \{show msg} failed with \{show errs}"
                   test <- anyM (checkError msg) errs
                   pure $ do -- Unless the error is the expected one
                             guard (not test)
                             -- We should complain we had the wrong one
                             pure (FailingWrongError fc msg (e ::: es)))
               (\err => do let Just msg = mmsg
                                 | _ => pure Nothing
                           log "elab.failing" 10 $ "Failing block based on \{show msg} failed with \{show err}"
                           test <- checkError msg err
                           pure $ do -- Unless the error is the expected one
                                     guard (not test)
                                     -- We should complain we had the wrong one
                                     pure (FailingWrongError fc msg (err ::: [])))
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
process eopts nest env (IClaim (MkFCVal fc (MkIClaimData rig vis opts ty)))
    = processType eopts nest env fc rig vis opts ty
process eopts nest env (IData fc vis mbtot ddef)
    = processData eopts nest env fc vis mbtot ddef
process eopts nest env (IDef fc fname def)
    = processDef eopts nest env fc fname def
process eopts nest env (IParameters fc ps decls)
    = processParams nest env fc (forget ps) decls
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
process eopts nest env (IPragma _ _ act)
    = act nest env
process eopts nest env (ILog lvl)
    = addLogLevel (uncurry unsafeMkLogLevel <$> lvl)
process eopts nest env (IBuiltin fc type name)
    = processBuiltin nest env fc type name

TTImp.Elab.Check.processDecl = process

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
    bindConNames (MkImpTy fc n ty)
        = do ty' <- bindTypeNames fc [] (toList vars) ty
             pure (MkImpTy fc n ty')

    bindDataNames : ImpData -> Core ImpData
    bindDataNames (MkImpData fc n t opts cons)
        = do t' <- traverseOpt (bindTypeNames fc [] (toList vars)) t
             cons' <- traverse bindConNames cons
             pure (MkImpData fc n t' opts cons')
    bindDataNames (MkImpLater fc n t)
        = do t' <- bindTypeNames fc [] (toList vars) t
             pure (MkImpLater fc n t')

    -- bind implicits to make raw TTImp source a bit friendlier
    bindNames : ImpDecl -> Core ImpDecl
    bindNames (IClaim (MkFCVal fc (MkIClaimData c vis opts (MkImpTy tfc n ty))))
        = do ty' <- bindTypeNames fc [] (toList vars) ty
             pure (IClaim (MkFCVal fc (MkIClaimData c vis opts (MkImpTy tfc n ty'))))
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
         Right (ws, decor, tti) <- logTime 0 "Parsing" $
                            coreLift $ parseFile fname (PhysicalIdrSrc modIdent)
                            (do decls <- prog (PhysicalIdrSrc modIdent)
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         traverse_ recordWarning ws
         logTime 0 "Elaboration" $
            catch (do ignore $ processTTImpDecls (MkNested []) ScopeEmpty tti
                      Nothing <- checkDelayedHoles
                          | Just err => throw err
                      pure True)
                  (\err => do coreLift_ (printLn err)
                              pure False)
