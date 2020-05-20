module TTImp.ProcessDecls

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.UnifyState

import Parser.Source

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.Parser
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessParams
import TTImp.ProcessRecord
import TTImp.ProcessTransform
import TTImp.ProcessType
import TTImp.TTImp

import Data.List

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
         extendNS (reverse ns)
         traverse_ (processDecl eopts nest env) decls
         defs <- get Ctxt
         put Ctxt (record { currentNS = cns } defs)
process eopts nest env (ITransform fc n lhs rhs)
    = processTransform eopts nest env fc n lhs rhs
process eopts nest env (IPragma act)
    = act nest env
process eopts nest env (ILog n)
    = setLogLevel n

TTImp.Elab.Check.processDecl = process

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
    bindConNames (MkImpTy fc n ty)
        = do ty' <- bindTypeNames [] vars ty
             pure (MkImpTy fc n ty')

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
    bindNames (IClaim fc c vis opts (MkImpTy tfc n ty))
        = do ty' <- bindTypeNames [] vars ty
             pure (IClaim fc c vis opts (MkImpTy tfc n ty'))
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
            catch (do processTTImpDecls (MkNested []) [] tti
                      Nothing <- checkDelayedHoles
                          | Just err => throw err
                      pure True)
                  (\err => do coreLift (printLn err)
                              pure False)
