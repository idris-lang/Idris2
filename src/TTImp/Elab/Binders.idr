module TTImp.Elab.Binders

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

-- Drop the name from the nested function declarations. We do this when
-- going into a new scope, so that we're resolving to the most recently
-- bound name.
export
dropName : Name -> NestedNames vars -> NestedNames vars
dropName n nest = { names $= drop } nest
  where
    drop : List (Name, a) -> List (Name, a)
    drop [] = []
    drop ((x, y) :: xs)
        = if x == n then drop xs
             else (x, y) :: drop xs

checkPiInfo : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              RigCount -> ElabInfo -> NestedNames vars -> Env Term vars ->
              PiInfo RawImp -> (expTy : Maybe (Glued vars)) ->
              Core (PiInfo (Term vars))
checkPiInfo rig elabinfo nest env Explicit exp = pure Explicit
checkPiInfo rig elabinfo nest env Implicit exp = pure Implicit
checkPiInfo rig elabinfo nest env AutoImplicit exp = pure AutoImplicit
checkPiInfo rig elabinfo nest env (DefImplicit t) exp
    = do (tv, _) <- check rig elabinfo nest env t exp
         pure (DefImplicit tv)

export
checkPi : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          RigCount -> ElabInfo ->
          NestedNames vars -> Env Term vars ->
          FC ->
          RigCount -> PiInfo RawImp -> (n : Name) ->
          (argTy : RawImp) -> (retTy : RawImp) ->
          (expTy : Maybe (Glued vars)) ->
          Core (Term vars, Glued vars)
checkPi rig elabinfo nest env fc rigf info n argTy retTy expTy
    = do let pirig = getRig (elabMode elabinfo)
         tyu <- uniVar fc
         (tyv, tyt) <- check pirig elabinfo nest env argTy
                             (Just (gType fc tyu))
         info' <- checkPiInfo rigf elabinfo nest env info (Just (gnf env tyv))
         let env' : Env Term (n :: _) = Pi fc rigf info' tyv :: env
         let nest' = weaken (dropName n nest)
         scu <- uniVar fc
         (scopev, scopet) <-
            inScope fc env' (\e' =>
              check {e=e'} pirig elabinfo nest' env' retTy (Just (gType fc scu)))
         -- TODO Cumulativity: tyu <= max, scu <= max
         piu <- uniVar fc
         checkExp rig elabinfo env fc (Bind fc n (Pi (getFC argTy) rigf info' tyv) scopev) (gType fc piu) expTy
  where
    -- Might want to match on the LHS, so use the context rig, otherwise
    -- it's always erased
    getRig : ElabMode -> RigCount
    getRig (InLHS _) = rig
    getRig _ = erased

findLamRig : {auto c : Ref Ctxt Defs} ->
             Maybe (Glued vars) -> Core RigCount
findLamRig Nothing = pure top
findLamRig (Just expty)
    = do tynf <- getNF expty
         case tynf of
              NBind _ _ (Pi _ c _ _) sc => pure c
              _ => pure top

inferLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
inferLambda rig elabinfo nest env fc rigl info n argTy scope expTy
    = do rigb_in <- findLamRig expTy
         let rigb = rigb_in `glb` rigl
         u <- uniVar fc
         (tyv, tyt) <- check erased elabinfo nest env argTy (Just (gType fc u))
         info' <- checkPiInfo rigl elabinfo nest env info (Just (gnf env tyv))
         let env' : Env Term (n :: _) = Lam fc rigb info' tyv :: env
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <- inScope fc env' (\e' =>
                                check {e=e'} rig elabinfo
                                      nest' env' scope Nothing)
         let lamty = gnf env (Bind fc n (Pi fc rigb info' tyv) !(getTerm scopet))
         logGlue "elab.binder" 5 "Inferred lambda type" env lamty
         maybe (pure ())
               (logGlueNF "elab.binder" 5 "Expected lambda type" env) expTy
         checkExp rig elabinfo env fc
                  (Bind fc n (Lam fc rigb info' tyv) scopev)
                  lamty expTy

getTyNF : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          Env Term vars -> Term vars -> Core (Term vars)
getTyNF env x@(Bind _ _ _ _) = pure x
getTyNF env x
    = do defs <- get Ctxt
         xnf <- nf defs env x
         empty <- clearDefs defs
         quote empty env xnf

export
checkLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope Nothing
    = let rig = if isErased rig_in then erased else linear in
          inferLambda rig elabinfo nest env fc rigl info n argTy scope Nothing
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope (Just expty_in)
    = do let rig = if isErased rig_in then erased else linear
         let solvemode = case elabMode elabinfo of
                              InLHS _ => inLHS
                              _ => inTerm
         solveConstraints solvemode Normal
         expty <- getTerm expty_in
         exptynf <- getTyNF env expty
         defs <- get Ctxt
         case exptynf of
              Bind bfc bn (Pi fc' c _ pty) psc =>
                 do u <- uniVar fc'
                    (tyv, tyt) <- check erased elabinfo nest env
                                        argTy (Just (gType fc u))
                    info' <- checkPiInfo rigl elabinfo nest env info (Just (gnf env tyv))
                    let rigb = rigl `glb` c
                    let env' : Env Term (n :: _) = Lam fc rigb info' tyv :: env
                    ignore $ convert fc elabinfo env (gnf env tyv) (gnf env pty)
                    let nest' = weaken (dropName n nest)
                    (scopev, scopet) <-
                       inScope fc env' (\e' =>
                          check {e=e'} rig elabinfo nest' env' scope
                                (Just (gnf env' (renameTop n psc))))
                    logTermNF "elab.binder" 10 "Lambda type" env exptynf
                    logGlueNF "elab.binder" 10 "Got scope type" env' scopet

                    -- Currently, the fc a PLam holds (and that ILam gets as a consequence)
                    -- is the file context of the argument to the lambda. This fits nicely
                    -- in this exact use, but is likely a bug.
                    log "metadata.names" 7 "checkLambda is adding ↓"
                    addNameType fc n env pty -- Add the type of the argument to the metadata

                    -- We've already checked the argument and scope types,
                    -- so we just need to check multiplicities
                    when (rigb /= c) $
                        throw (CantConvert fc (gamma defs) env
                                  (Bind fc n (Pi fc' rigb info' tyv) !(getTerm scopet))
                                  (Bind fc bn (Pi fc' c info' pty) psc))
                    pure (Bind fc n (Lam fc' rigb info' tyv) scopev,
                          gnf env (Bind fc n (Pi fc' rigb info' tyv) !(getTerm scopet)))
              _ => inferLambda rig elabinfo nest env fc rigl info n argTy scope (Just expty_in)

weakenExp : {x, vars : _} ->
            Env Term (x :: vars) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (x :: vars)))
weakenExp env Nothing = pure Nothing
weakenExp env (Just gtm)
    = do tm <- getTerm gtm
         pure (Just (gnf env (weaken tm)))

export
checkLet : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> (lhsFC : FC) -> RigCount -> (n : Name) ->
           (nTy : RawImp) -> (nVal : RawImp) -> (scope : RawImp) ->
           (expTy : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkLet rigc_in elabinfo nest env fc lhsFC rigl n nTy nVal scope expty {vars}
    = do let rigc = if isErased rigc_in then erased else linear
         u <- uniVar fc
         (tyv, tyt) <- check erased elabinfo nest env nTy (Just (gType fc u))
         -- Try checking at the given multiplicity; if that doesn't work,
         -- try checking at Rig1 (meaning that we're using a linear variable
         -- so the resulting binding should be linear)
         -- Also elaborate any case blocks in the value via runDelays
         (valv, valt, rigb) <- handle
              (do c <- runDelays (==CaseBlock) $ check (rigl |*| rigc)
                             ({ preciseInf := True } elabinfo)
                             nest env nVal (Just (gnf env tyv))
                  pure (fst c, snd c, rigl |*| rigc))
              (\err => case linearErr err of
                            Just r
                              => do branchOne
                                     (do c <- runDelays (==CaseBlock) $ check linear elabinfo
                                                  nest env nVal (Just (gnf env tyv))
                                         pure (fst c, snd c, linear))
                                     (do c <- check (rigl |*| rigc)
                                                  elabinfo -- without preciseInf
                                                  nest env nVal (Just (gnf env tyv))
                                         pure (fst c, snd c, rigMult rigl rigc))
                                     r
                            _ => do c <- check (rigl |*| rigc)
                                               elabinfo -- without preciseInf
                                               nest env nVal (Just (gnf env tyv))
                                    pure (fst c, snd c, rigl |*| rigc))
         let env' : Env Term (n :: _) = Lam fc rigb Explicit tyv :: env
         let nest' = weaken (dropName n nest)
         expScope <- weakenExp env' expty
         (scopev, gscopet) <-
            inScope fc env' (\e' =>
              check {e=e'} rigc elabinfo nest' env' scope expScope)
         scopet <- getTerm gscopet

         -- No need to 'checkExp' here - we've already checked scopet
         -- against the expected type when checking the scope, so just
         -- build the term directly

         -- Add the lhs of the let to metadata
         log "metadata.names" 7 $ "checkLet is adding ↓"
         addNameType lhsFC n env tyv

         pure (Bind fc n (Let fc rigb valv tyv) scopev,
               gnf env (Bind fc n (Let fc rigb valv tyv) scopet))
  where
    linearErr : Error -> Maybe RigCount
    linearErr (LinearMisuse _ _ r _) = Just r
    linearErr (InType _ _ e) = linearErr e
    linearErr (InCon _ _ e) = linearErr e
    linearErr (InLHS _ _ e) = linearErr e
    linearErr (InRHS _ _ e) = linearErr e
    linearErr _ = Nothing
