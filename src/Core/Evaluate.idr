module Core.Evaluate

import Core.Context
import Core.Context.Log
import Core.Options.Log
import Core.Env
import public Core.Evaluate.Convert
import public Core.Evaluate.Normalise
import public Core.Evaluate.Quote
import public Core.Evaluate.Value
import Core.Evaluate.Expand
import Core.TT

import Data.SnocList

parameters {auto c : Ref Ctxt Defs}

  recompute : {vars: _} -> Env Term vars -> NF vars -> Core (NF vars)
  recompute env val = do
    tm <- quote env val
    expand !(nf env tm)

  export
  touch : {vars: _} -> Env Term vars -> NF vars -> Core (NF vars)
  touch env val@(VMeta{}) = recompute env val
  touch env val@(VApp{}) = recompute env val
  touch env val = pure val

  export
  normalise : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normalise env tm
      = do val <- nf env tm
           quoteNF env val

  export
  normaliseHNF : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseHNF env tm
      = do val <- nf env tm
           quoteHNF env val

  export
  normaliseAll : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseAll env tm
      = do val <- nf env tm
           quoteNFall env val

  export
  normaliseHNFall : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseHNFall env tm
      = do val <- nf env tm
           quoteHNFall env val

  export
  normaliseHoles : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseHoles env tm
      = do val <- nfHoles env tm
           quoteHoles env val

  export
  normaliseLHS : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseLHS env tm
      = quoteHoles env !(nfLHS env tm)

  export
  normaliseBinders : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseBinders env tm
      = do val <- nf env tm
           quoteBinders env val

  -- Normalise, but without normalising the types of binders.
  export
  normaliseScope : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseScope env (Bind fc n b sc)
      = pure $ Bind fc n b !(normaliseScope (env :< b) sc)
  normaliseScope env tm = normalise env tm

  export
  normaliseHolesScope : {vars: _} -> Env Term vars -> Term vars -> Core (Term vars)
  normaliseHolesScope env (Bind fc n b sc)
      = pure $ Bind fc n b !(normaliseHolesScope (env :< b) sc)
  normaliseHolesScope env tm = normaliseHoles env tm

  export
  getArityVal : {vars: _} -> NF vars -> Core Nat
  getArityVal (VBind fc _ (Pi _ _ _ _) sc)
      = pure $ 1 + !(getArityVal !(expand !(sc (pure (VErased fc Placeholder)))))
  getArityVal _ = pure 0

  export
  getArity : {vars: _} -> Env Term vars -> Term vars -> Core Nat
  getArity env tm = getArityVal !(expand !(nf env tm))


  -- If the term is an application of a primitive conversion (fromInteger etc)
  -- and it's applied to a constant, fully normalise the term.
  export
  normalisePrims : {vs : _} ->
                   -- size heuristic for when to unfold
                   (Constant -> Bool) ->
                   -- view to check whether an argument is a constant
                   (arg -> Maybe Constant) ->
                   -- Reduce everything (True) or just public export (False)
                   Bool ->
                   -- list of primitives
                   List Name ->
                   -- view of the potential redex
                   (n : Name) ->          -- function name
                   (args : SnocList arg) ->   -- arguments from inside out (arg1, ..., argk)
                   -- actual term to evaluate if needed
                   (tm : Term vs) ->      -- original term (n arg1 ... argk)
                   Env Term vs ->         -- evaluation environment
                   -- output only evaluated if primitive
                   Core (Maybe (Term vs))
  normalisePrims boundSafe viewConstant all prims n args tm env
     = do let True = isPrimName prims !(getFullName n) -- is a primitive
                | _ => pure Nothing
          let (_ :< mc) = reverse args -- with at least one argument
                | _ => pure Nothing
          let (Just c) = viewConstant mc -- that is a constant
                | _ => pure Nothing
          let True = boundSafe c -- that we should expand
                | _ => pure Nothing
          tm <- if all
                   then normaliseAll env tm
                   else normalise env tm
          pure (Just tm)

  export
  etaContract : {vars : _} -> Term vars -> Core (Term vars)
  etaContract tm = do
    defs <- get Ctxt
    logTerm "eval.eta" 5 "Attempting to eta contract subterms of" tm
    nf <- normalise (mkEnv EmptyFC _) tm
    logTerm "eval.eta" 5 "Evaluated to" nf
    res <- mapTermM act tm
    logTerm "eval.eta" 5 "Result of eta-contraction" res
    pure res

     where

      act : {vars : _} -> Term vars -> Core (Term vars)
      act tm = do
        logTerm "eval.eta" 10 "  Considering" tm
        case tm of
          (Bind _ x (Lam _ _ _ _) (App _ fn _ (Local _ _ Z _))) => do
            logTerm "eval.eta" 10 "  Shrinking candidate" fn
            let shrunk = shrinkTerm fn (Drop Refl)
            case shrunk of
              Nothing => do
                log "eval.eta" 10 "  Failure!"
                pure tm
              Just tm' => do
                logTerm "eval.eta" 10 "  Success!" tm'
                pure tm'
          _ => pure tm

  export
  logValue : {vars : _} ->
          LogTopic -> Nat -> Lazy String -> Value f vars -> Core ()
  logValue s n msg tmnf
      = when !(logging s n) $
          do defs <- get Ctxt
             tmnf' <- toFullNames tmnf
             depth <- getDepth
             logString depth s.topic n (msg ++ ": " ++ show tmnf')

  -- Log message with a value, translating back to human readable names first
  export
  logNF : {vars : _} ->
          LogTopic -> Nat -> Lazy String -> Env Term vars -> Value f vars -> Core ()
  logNF s n msg env tmnf
      = when !(logging s n) $
          do defs <- get Ctxt
             tm <- logQuiet $ quote env tmnf
             tm' <- toFullNames tm
             depth <- getDepth
             logString depth s.topic n (msg ++ ": " ++ show tm')

  -- Log message with a term, reducing holes and translating back to human
  -- readable names first
  -- export
  logTermNF' : {vars : _} ->
               LogTopic ->
               Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
  logTermNF' s n msg env tm
      = do defs <- get Ctxt
           tmnf <- logQuiet $ normalise env tm
           tm' <- toFullNames tmnf
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

  export
  logTermNF : {vars : _} ->
              LogTopic ->
              Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
  logTermNF s n msg env tm
      = when !(logging s n) $ logTermNF' s n msg env tm

  export
  logEnv : {vars : _} ->
           LogTopic ->
           Nat -> String -> Env Term vars -> Core ()
  logEnv s n msg env
      = when !(logging s n) $
          do depth <- getDepth
             logString depth s.topic n msg
             dumpEnv env
    where
      dumpEnv : {vs : SnocList Name} -> Env Term vs -> Core ()
      dumpEnv [<] = pure ()
      dumpEnv {vs = _ :< x} (bs :< Let _ c val ty)
          = do logTermNF' s n (msg ++ ": let " ++ show x) bs val
               logTermNF' s n (msg ++ ":" ++ show c ++ " " ++ show x) bs ty
               dumpEnv bs
      dumpEnv {vs = _ :< x} (bs :< b)
          = do logTermNF' s n (msg ++ ":" ++ show (multiplicity b) ++ " " ++
                             show (piInfo b) ++ " " ++
                             show x) bs (binderType b)
               dumpEnv bs

  -- Return a new term, and whether any updates were made. If no updates were
  -- made, we should stick with the original term (so no unnecessary expansion)
  -- of App
  replace'
      : {vars: _} -> (expandGlued : Bool) -> Int -> Env Term vars ->
        (orig : Value f vars) -> (parg : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars, Bool)
  replace' {vars} expand tmpi env orig parg tm
      = do ok <- convert env orig tm
           if ok
              then pure (parg, True)
              else repSub tm
    where
      repArg : forall f . Value f vars -> Core (Term vars, Bool)
      repArg = replace' expand tmpi env orig parg

      repArgAll : Spine vars -> Core (SnocList (FC, RigCount, Term vars), Bool)
      repArgAll [<] = pure ([<], False)
      repArgAll (xs :< MkSpineEntry f r tm)
          = do (xs', upd) <- repArgAll xs
               (tm', upd') <- repArg !tm
               pure (xs' :< (f, r, tm'), upd || upd')

      repScope : FC -> Int -> (args : SnocList (RigCount, Name)) ->
                 VCaseScope args vars -> Core (CaseScope vars, Bool)
      repScope fc tmpi [<] rhs
          = do -- Stop expanding or recursive functions will go forever
               (rhs', u) <- replace' False tmpi env orig parg (snd !rhs)
               pure (RHS [] rhs', u) -- Forced equalities thrown away now
      repScope fc tmpi (xs :< (r, x)) scope
          = do let xn = MN "tmpsc" tmpi
               let xv = vRef fc Bound xn
               (scope', u) <- repScope fc (tmpi + 1) xs (scope (pure xv))
               pure (Arg r x (refsToLocalsCaseScope (Add x xn None) scope'), u)

      repAlt : VCaseAlt vars -> Core (CaseAlt vars, Bool)
      repAlt (VConCase fc n t args scope)
          = do (scope', u) <- repScope fc tmpi args scope
               pure (ConCase fc n t scope', u)
      repAlt (VDelayCase fc ty arg scope)
          = do let tyn = MN "tmpd" tmpi
               let argn = MN "tmpd" (tmpi + 1)
               let tyv = vRef fc Bound tyn
               let argv = vRef fc Bound argn
               -- Stop expanding or recursive functions will go forever
               (scope', u) <- replace' False (tmpi + 2) env orig parg
                                       (snd !(scope (pure tyv) (pure argv)))
               let rhs = refsToLocals (Add arg argn (Add ty tyn None)) scope'
               pure (DelayCase fc ty arg rhs, u)
      repAlt (VConstCase fc c rhs)
          = do (rhs', u) <- repArg rhs
               pure (ConstCase fc c rhs', u)
      repAlt (VDefaultCase fc rhs)
          = do (rhs', u) <- repArg rhs
               pure (DefaultCase fc rhs', u)

      repSub : forall f . Value f vars -> Core (Term vars, Bool)

      repPiInfo : forall f . PiInfo (Value f vars) -> Core (PiInfo (Term vars), Bool)
      repPiInfo Explicit = pure (Explicit, False)
      repPiInfo Implicit = pure (Implicit, False)
      repPiInfo AutoImplicit = pure (AutoImplicit, False)
      repPiInfo (DefImplicit t)
         = do (t', u) <- repSub t
              pure (DefImplicit t', u)

      repBinder : forall f . Binder (Value f vars) -> Core (Binder (Term vars), Bool)
      repBinder (Lam fc c p ty)
          = do (p', u) <- repPiInfo p
               (ty', u') <- repSub ty
               pure (Lam fc c p' ty', u || u')
      repBinder (Let fc c val ty)
          = do (val', u) <- repSub val
               (ty', u') <- repSub ty
               pure (Let fc c val' ty', u || u')
      repBinder (Pi fc c p ty)
          = do (p', u) <- repPiInfo p
               (ty', u') <- repSub ty
               pure (Pi fc c p' ty', u || u')
      repBinder (PVar fc c p ty)
          = do (p', u) <- repPiInfo p
               (ty', u') <- repSub ty
               pure (PVar fc c p' ty', u || u')
      repBinder (PLet fc c val ty)
          = do (val', u) <- repSub val
               (ty', u') <- repSub ty
               pure (PLet fc c val' ty', u || u')
      repBinder (PVTy fc c ty)
          = do (ty', u) <- repSub ty
               pure (PVTy fc c ty', u)

      repSub (VBind fc x b scfn)
          = do (b', u) <- repBinder b
               let x' = MN "tmpb" tmpi
               let var = vRef fc Bound x'
               (sc', u') <- replace' expand (tmpi + 1) env orig parg !(scfn (pure var))
               pure (Bind fc x b' (refsToLocals (Add x x' None) sc'), u || u')
      repSub (VApp fc nt fn args val')
          = do fl <- getFlags fn
               if expand && not (BlockReduce `elem` fl)
                 then do Just nf <- val'
                              | Nothing =>
                               do (args', u) <- repArgAll args
                                  pure (applyStackWithFC (Ref fc nt fn) (toList args'), u)
                         if !(blockedApp nf)
                             then
                                 do (args', u) <- repArgAll args
                                    pure (applyStackWithFC (Ref fc nt fn) (toList args'), u)
                              else
                                 do (tm', u) <- replace' expand tmpi env orig parg nf
                                    if u
                                       then pure (tm', u)
                                       else do (args', u) <- repArgAll args
                                               pure (applyStackWithFC (Ref fc nt fn) (toList args'), u)
                 else do (args', u) <- repArgAll args
                         pure (applyStackWithFC (Ref fc nt fn) (toList args'), u)
        where
          getFlags : Name -> Core (List DefFlag)
          getFlags fn
              = do defs <- get Ctxt
                   Just gdef <- lookupCtxtExact fn (gamma defs)
                        | Nothing => pure []
                   pure (flags gdef)

          blockedApp : forall f . Value f vars -> Core Bool
          blockedApp (VBind fc _ (Lam {}) sc)
              = blockedApp !(sc $ pure $ VErased fc Placeholder)
          blockedApp (VCase _ PatMatch _ _ _ _) = pure True
          blockedApp (VPrimOp{}) = pure True
          blockedApp _ = pure False
      repSub (VLocal fc idx p args)
          = do (args', u) <- repArgAll args
               pure (applyStackWithFC (Local fc Nothing idx p) (toList args'), u)
      -- Look in value of the metavar if it's solved, otherwise leave it
      repSub (VMeta fc n i scope args val)
          = do Nothing <- val
                   | Just val' => repSub val'
               sc' <- traverse (\ (q, tm) => do (tm', u) <- repArg !tm
                                                pure ((q, tm'), u)) scope
               (args', u) <- repArgAll args
               let u' = or (map (\x => Delay x) (map snd sc'))
               pure (applyStackWithFC (Meta fc n i (map fst sc')) (toList args'), u || u')
      repSub (VDCon fc n t a args)
        = do (args', u) <- repArgAll args
             pure (applyStackWithFC (Ref fc (DataCon t a) n) (toList args'), u)
      repSub (VTCon fc n a args)
        = do (args', u) <- repArgAll args
             pure (applyStackWithFC (Ref fc (TyCon a) n) (toList args'), u)
      repSub (VAs fc s a pat)
          = do (a', u) <- repSub a
               (pat', u') <- repSub pat
               pure (As fc s a' pat',  u || u')
      repSub (VCase fc t r sc scty alts)
          = do (sc', u) <- repArg sc
               (scty', u') <- repArg scty
               alts'  <- traverse repAlt alts
               let u'' = or (map (\x => Delay x) (map snd alts'))
               pure (Case fc t r sc' scty' (map fst alts'), u || u' || u'')
      repSub (VDelayed fc r tm)
          = do (tm', u) <- repSub tm
               pure (TDelayed fc r tm', u)
      repSub (VDelay fc r ty tm)
          = do (ty', u) <- repArg ty
               (tm', u') <- repArg tm
               pure (TDelay fc r ty' tm', u || u')
      repSub (VForce fc r tm args)
          = do (args', u) <- repArgAll args
               (tm', u') <- repSub tm
               pure $ (applyStackWithFC (TForce fc r tm') (toList args'), u || u')
      repSub tm = pure (!(quote env tm), False)

  export
  replace
      : {vars: _} -> Env Term vars ->
        (orig : Value f vars) -> (new : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars)
  replace env orig new tm
      = do (tm', _) <- replace' True 0 env orig new tm
           pure tm'

  export
  replaceSyn
      : {vars: _} -> Env Term vars ->
        (orig : Value f vars) -> (new : Term vars) -> (tm : Value f' vars) ->
        Core (Term vars)
  replaceSyn env orig new tm
      = do (tm', _) <- replace' False 0 env orig new tm
           pure tm'

export
gErased : FC -> Glued vars
gErased fc = VErased fc Placeholder

export
gType : FC -> Name -> Glued vars
gType fc u = VType fc u

export
gUnmatched : FC -> String -> Glued vars
gUnmatched fc msg = VUnmatched fc msg
