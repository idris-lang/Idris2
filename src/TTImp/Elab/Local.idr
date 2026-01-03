module TTImp.Elab.Local

import Core.Env
import Core.Metadata
import Core.Unify

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.TTImp

import Libraries.Data.NameMap
import Libraries.Data.WithDefault

%default covering

export
localHelper : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             NestedNames vars -> Env Term vars ->
             List ImpDecl -> (NestedNames vars -> Core a) ->
             Core a
localHelper {vars} nest env nestdecls_in func
    = do est <- get EST
         let f = defining est
         defs <- get Ctxt
         gdef <- lookupCtxtExact (Resolved (defining est)) (gamma defs)
         let vis  = maybe Public (collapseDefault . visibility) gdef
         let mult = maybe linear GlobalDef.multiplicity gdef

         -- If the parent function is public, the nested definitions need
         -- to be public too
         let nestdeclsVis =
               if vis == Public
                  then map setPublic nestdecls_in
                  else nestdecls_in

         -- If the parent function is erased, then the nested definitions
         -- will be erased too
         let nestdeclsMult =
           if mult == erased
              then map setErased nestdeclsVis
              else nestdeclsVis

         let defNames = definedInBlock emptyNS nestdeclsMult
         names' <- traverse (applyEnv f) defNames
         let nest' = { names $= (names' ++) } nest
         -- TODO is this comment still up-to-date?
         -- For the local definitions, don't allow access to linear things
         -- unless they're explicitly passed.
         -- This is because, at the moment, we don't have any mechanism of
         -- ensuring the nested definition is used exactly once
         let env' = eraseLinear env
         -- We don't want to keep rechecking delayed elaborators in the
         -- locals block, because they're not going to make progress until
         -- we come out again, so save them
         ust <- get UST
         let olddelayed = delayedElab ust
         put UST ({ delayedElab := [] } ust)
         defs <- get Ctxt
         -- store the local hints, so we can reset them after we've elaborated
         -- everything
         let oldhints = localHints defs

         let nestdecls = map (updateName nest') nestdeclsMult
         log "elab.def.local" 20 $ show nestdecls

         traverse_ (processDecl [] nest' env') nestdecls
         update UST { delayedElab := olddelayed }
         res <- func nest'
         update Ctxt { localHints := oldhints }
         pure res
  where
    applyEnv : Int -> Name ->
               Core (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars))
    applyEnv outer inner
          = do ust <- get UST
               put UST ({ nextName $= (+1) } ust)
               let nestedName_in = Nested (outer, nextName ust) inner
               nestedName <- inCurrentNS nestedName_in
               n' <- addName nestedName
               pure (inner, (Just nestedName, VarSet.asList $ allVars env,
                        \fc, nt => applyToFull fc
                               (Ref fc nt (Resolved n')) env))

    -- Update the names in the declarations to the new 'nested' names.
    -- When we encounter the names in elaboration, we'll update to an
    -- application of the nested name.
    updateTyName : NestedNames vars -> ImpTy -> ImpTy
    updateTyName nest ty
        = update "tyname" (map (mapNestedName nest)) ty

    updateDataName : NestedNames vars -> ImpData -> ImpData
    updateDataName nest (MkImpData loc' n tycons dopts dcons)
        = MkImpData loc' (mapNestedName nest n) tycons dopts
                         (map (updateTyName nest) dcons)
    updateDataName nest (MkImpLater loc' n tycons)
        = MkImpLater loc' (mapNestedName nest n) tycons

    updateFieldName : NestedNames vars -> IField -> IField
    updateFieldName nest field
        = update "name" (map (mapNestedName nest)) field

    updateRecordName : NestedNames vars -> ImpRecordData Name -> ImpRecordData Name
    updateRecordName nest (MkImpRecord header body)
        = let updatedTyName = (update "name" (map (mapNestedName nest)) header)
              updatedConName = (update "name" (map (mapNestedName nest)) body)
              updatedParameters = (map (map (updateFieldName nest)) updatedConName)
          in MkImpRecord updatedTyName updatedParameters

    updateRecordNS : NestedNames vars -> Maybe String -> Maybe String
    updateRecordNS _    Nothing   = Nothing
    updateRecordNS nest (Just ns) = Just $ show $ mapNestedName nest (UN $ mkUserName ns)

    updateName : NestedNames vars -> ImpDecl -> ImpDecl
    updateName nest (IClaim claim)
         = IClaim $ map {type $= updateTyName nest} claim
    updateName nest (IDef loc' n cs)
         = IDef loc' (mapNestedName nest n) cs
    updateName nest (IData loc' vis mbt d)
         = IData loc' vis mbt (updateDataName nest d)
    updateName nest (IRecord loc' ns vis mbt imprecord)
         = IRecord loc' (updateRecordNS nest ns) vis mbt (map (updateRecordName nest) imprecord)
    updateName nest i = i

    setPublic : ImpDecl -> ImpDecl
    setPublic (IClaim claim)
        = IClaim $ map {vis := Public} claim
    setPublic (IData fc _ mbt d) = IData fc (specified Public) mbt d
    setPublic (IRecord fc c _ mbt r) = IRecord fc c (specified Public) mbt r
    setPublic (IParameters fc ps decls)
        = IParameters fc ps (map setPublic decls)
    setPublic (INamespace fc ps decls)
        = INamespace fc ps (map setPublic decls)
    setPublic d = d

    setErased : ImpDecl -> ImpDecl
    setErased (IClaim claim)
        = IClaim $ map {rig := erased} claim
    setErased (IParameters fc ps decls)
        = IParameters fc ps (map setErased decls)
    setErased (INamespace fc ps decls)
        = INamespace fc ps (map setErased decls)
    setErased d = d

export
checkLocal : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> List ImpDecl -> (scope : RawImp) ->
             (expTy : Maybe (Glued vars)) ->
             Core (Term vars, Glued vars)
checkLocal {vars} rig elabinfo nest env fc nestdecls_in scope expty
    = localHelper nest env nestdecls_in $ \nest' => check rig elabinfo nest' env scope expty

getLocalTerm : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               FC -> Env Term vars -> Term vars -> List Name ->
               Core (Term vars, List (Var vars))
getLocalTerm fc env f [] = pure (f, [])
getLocalTerm fc env f (a :: as)
    = case defined a env of
           Just (MkIsDefined rigb lv) =>
                do (tm, vs) <- getLocalTerm fc env
                                   (App fc f (Local fc Nothing _ lv)) as
                   pure (tm, MkVar lv :: vs)
           Nothing => throw (InternalError "Case Local failed")

export
checkCaseLocal : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> Name -> Name -> List Name -> RawImp ->
                 (expTy : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
checkCaseLocal {vars} rig elabinfo nest env fc uname iname args sc expty
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact iname (gamma defs)
              | Nothing => check rig elabinfo nest env sc expty
         let nt = getDefNameType def
         let name = Ref fc nt iname
         (app, args) <- getLocalTerm fc env name args
         log "elab.local" 5 $ "Updating case local " ++ show uname ++ " " ++ show args
         logTermNF "elab.local" 5 "To" env app
         let nest' = { names $= ((uname, (Just iname, args,
                                         (\fc, nt => app))) :: ) }
                     nest
         check rig elabinfo nest' env sc expty
