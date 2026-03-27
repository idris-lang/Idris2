module Core.Erase

-- Erase 0-mulitplicity arguments from runtime terms
-- Assumption: Terms are already type correct

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT

import Data.SnocList


parameters {auto c : Ref Ctxt Defs}

  echeck : {vars : _} ->
           RigCount -> Env Term vars -> Term vars -> Core (Term vars)

  echeckAlt : {vars : _} ->
              -- must be Rig0 or Rig1
              (rhsrig : RigCount) ->
              Env Term vars ->
              (scrig : RigCount) ->
              CaseAlt vars ->
              Core (CaseAlt vars)
  echeckAlt rig env scrig (ConCase fc n t sc)
      = pure $ ConCase fc n t !(echeckScope env sc)
    where
      echeckScope : {vars : _} -> Env Term vars -> CaseScope vars ->
                    Core (CaseScope vars)
      echeckScope env (RHS _ tm) = pure $ RHS [] !(echeck rig env tm)
      echeckScope env (Arg c x sc)
            -- We don't have the type of the argument, but the good news is
            -- that we don't need it because we only need multiplicities and
            -- they are cached in App nodes.
          = do let env'
                   = env :<
                     PVar fc (rigMult scrig c) Explicit (Erased fc Placeholder)
               sc' <- echeckScope env' sc
               pure (Arg c x sc')
  echeckAlt rig env scrig (DelayCase fc t a rhs)
      = do -- See above for why the types are erased
           let env'
               = env :<
                 PVar fc erased Implicit (Erased fc Placeholder) :<
                 PVar fc scrig Explicit (Erased fc Placeholder)
           rhs' <- echeck rig env' rhs
           pure (DelayCase fc t a rhs')
  echeckAlt rig env scrig (ConstCase fc c rhs)
      = pure $ ConstCase fc c !(echeck rig env rhs)
  echeckAlt rig env scrig (DefaultCase fc rhs)
      = pure $ DefaultCase fc !(echeck rig env rhs)

  echeckAlts : {vars : _} ->
               (rhsrig : RigCount) ->
               Env Term vars ->
               (scrig : RigCount) ->
               List (CaseAlt vars) ->
               Core (List (CaseAlt vars))
  echeckAlts rig env scrig [] = pure []
  echeckAlts rig env scrig (a :: alts)
     = do a' <- echeckAlt rig env scrig a
          alts' <- echeckAlts rig env scrig alts
          pure (a' :: alts')

  echeckBinder : {vars : _} ->
           RigCount -> Env Term vars -> Binder (Term vars) ->
           Core (Binder (Term vars))
  echeckBinder rig env (Lam fc c p ty) = pure $ Lam fc c p ty
  echeckBinder rig env (Let fc c val ty)
      = do val' <- echeck (rigMult rig c) env val
           pure (Let fc c val' ty)
  echeckBinder rig env (Pi fc c p ty)
      = do ty' <- echeck (rigMult rig c) env ty
           pure (Pi fc c p ty')
  echeckBinder rig env (PVar fc c p ty)
      = pure (PVar fc c p ty)
  echeckBinder rig env (PLet fc c val ty)
      = do val' <- echeck (rigMult rig c) env val
           pure (PLet fc c val' ty)
  echeckBinder rig env (PVTy fc c ty)
      = pure (PVTy fc c ty)

  echeck rig env (Meta fc n i args)
      = do args' <- traverse (\ (c, arg) => do
                           let argRig = rigMult rig c
                           if isErased argRig
                              then pure (c, Erased fc Placeholder)
                              else do arg' <- echeck (rigMult rig c) env arg
                                      pure (c, arg')) args
           pure (Meta fc n i args')
  echeck rig_in env (Bind fc nm b sc)
      = do b' <- echeckBinder rig env b

           -- Anything linear can't be used in the scope of a let/lambda, if
           -- we're checking in general context
           let (env', rig') = case b of
                                   Pi _ _ _ _ => (env, rig)
                                   _ => (restrictEnv env rig, presence rig)

           sc' <- echeck rig' (env' :< b) sc
           pure (Bind fc nm b' sc')
    where
      rig : RigCount
      rig = case b of
                 Pi _ _ _ _ =>
                      if isErased rig_in
                         then erased
                         else top -- checking as if an inspectable run-time type
                 _ => rig_in
  echeck rig env (App fc fn q arg)
      = do fn' <- echeck rig env fn
           let argRig = rigMult rig q
           arg' <- if isErased argRig
                      then pure $ Erased fc Placeholder
                      else echeck (rigMult rig q) env arg
           pure (App fc fn' q arg')
  echeck rig env (As fc s var pat)
      = pure (As fc s !(echeck rig env var) !(echeck rig env pat))
  echeck rig env (Case fc ct scrig sc ty alts)
      = do sc' <- echeck (rigMult scrig rig) env sc
           alts' <- echeckAlts (presence rig) (restrictEnv env rig) scrig alts
           pure (Case fc ct scrig sc' ty alts')
  echeck rig env (TDelay fc r ty arg)
      = pure (TDelay fc r ty !(echeck rig env arg))
  echeck rig env (TForce fc r tm) = pure (TForce fc r !(echeck rig env tm))
  echeck rig env (Erased fc (Dotted t))
     = pure (Erased fc (Dotted !(echeck rig env t)))
  echeck rig env tm = pure tm

  export
  erase : {vars : _} ->
          RigCount -> Env Term vars -> Term vars -> Core (Term vars)
  erase = echeck
