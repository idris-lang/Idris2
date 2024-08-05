module Core.Transform

import Core.Context
import Core.Env
import Core.TT

import Libraries.Data.NameMap

%default total

unload : List (FC, Term vars) -> Term vars -> Term vars
unload [] fn = fn
unload ((fc, arg) :: args) fn = unload args (App fc fn arg)

-- List of matches on LHS
data MatchVars : ScopedList Name -> ScopedList Name -> Type where
     None : MatchVars lhsvars vs
     Match : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> Term vs ->
             MatchVars lhsvars vs -> MatchVars lhsvars vs

lookupMatch : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> MatchVars lhsvars vs ->
              Maybe (Term vs)
lookupMatch idx p None = Nothing
lookupMatch idx p (Match v _ val rest)
    = if idx == v
         then Just val
         else lookupMatch idx p rest

addMatch : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> Term vs ->
           MatchVars lhsvars vs -> Maybe (MatchVars lhsvars vs)
addMatch idx p val ms
    = case lookupMatch idx p ms of
           Nothing => Just (Match idx p val ms)
           Just val' => if eqTerm val val'
                           then Just ms
                           else Nothing

-- LHS of a rule must be a function application, so there's not much work
-- to do here!
match : MatchVars vars vs ->
        Term vars -> Term vs -> Maybe (MatchVars vars vs)
match ms (Local _ _ idx p) val
    = addMatch idx p val ms
match ms (App _ f a) (App _ f' a')
    = do ms' <- match ms f f'
         match ms' a a'
match ms x y
    = if eqTerm x y
         then Just ms
         else Nothing

covering
tryReplace : MatchVars vars vs -> Term vars -> Maybe (Term vs)
tryReplace ms (Local _ _ idx p) = lookupMatch idx p ms
tryReplace ms (Ref fc nt n) = pure (Ref fc nt n)
tryReplace ms (Meta fc n i as)
    = do as' <- traverse (tryReplace ms) as
         pure (Meta fc n i as')
tryReplace ms (Bind fc x b sc)
    = Nothing -- TODO: can't do this yet... need to be able to weaken ms
              -- Rules are unlikely to have binders usually but we should
              -- still support it eventually
tryReplace ms (App fc f a)
    = do f' <- tryReplace ms f
         a' <- tryReplace ms a
         pure (App fc f' a')
tryReplace ms (As fc s a p)
    = do a' <- tryReplace ms a
         p' <- tryReplace ms p
         pure (As fc s a' p')
tryReplace ms (TDelayed fc r tm)
    = do tm' <- tryReplace ms tm
         pure (TDelayed fc r tm')
tryReplace ms (TDelay fc r ty tm)
    = do ty' <- tryReplace ms ty
         tm' <- tryReplace ms tm
         pure (TDelay fc r ty' tm')
tryReplace ms (TForce fc r tm)
    = do tm' <- tryReplace ms tm
         pure (TForce fc r tm')
tryReplace ms (PrimVal fc c) = pure (PrimVal fc c)
tryReplace ms (Erased fc Impossible) = pure (Erased fc Impossible)
tryReplace ms (Erased fc Placeholder) = pure (Erased fc Placeholder)
tryReplace ms (Erased fc (Dotted t)) = Erased fc . Dotted <$> tryReplace ms t
tryReplace ms (TType fc u) = pure (TType fc u)

covering
tryApply : Transform -> Term vs -> Maybe (Term vs)
tryApply trans@(MkTransform {vars} n _ lhs rhs) tm
   = case match None lhs tm of
          Just ms => tryReplace ms rhs
          Nothing =>
            case tm of
                 App fc f a =>
                     do f' <- tryApply trans f
                        Just (App fc f' a)
                 _ => Nothing

covering
apply : List Transform -> Term vars -> (Bool, Term vars)
apply [] tm = (False, tm)
apply (t :: ts) tm
    = case tryApply t tm of
           Nothing => apply ts tm
           Just res => (True, res)

data Upd : Type where

covering
trans : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref Upd Bool} ->
        Env Term vars -> List (FC, Term vars) -> Term vars ->
        Core (Term vars)
trans env stk (Ref fc Func fn)
    = do defs <- get Ctxt
         case lookup fn (transforms defs) of
              Nothing => pure (unload stk (Ref fc Func fn))
              Just ts => do let fullapp = unload stk (Ref fc Func fn)
                            let (u, tm') = apply ts fullapp
                            update Upd (|| u)
                            pure tm'
trans env stk (Meta fc n i args)
    = do args' <- traverse (trans env []) args
         pure $ unload stk (Meta fc n i args')
trans env stk (Bind fc x b sc)
    = do b' <- traverse (trans env []) b
         sc' <- trans (b' :: env) [] sc
         pure $ unload stk (Bind fc x b' sc')
trans env stk (App fc fn arg)
    = do arg' <- trans env [] arg
         trans env ((fc, arg') :: stk) fn
trans env stk (TDelayed fc r tm)
    = do tm' <- trans env [] tm
         pure $ unload stk (TDelayed fc r tm')
trans env stk (TDelay fc r ty tm)
    = do ty' <- trans env [] ty
         tm' <- trans env [] tm
         pure $ unload stk (TDelay fc r ty' tm')
trans env stk (TForce fc r tm)
    = do tm' <- trans env [] tm
         pure $ unload stk (TForce fc r tm')
trans env stk tm = pure $ unload stk tm

covering
transLoop : {auto c : Ref Ctxt Defs} ->
            Nat -> Env Term vars -> Term vars -> Core (Term vars)
transLoop Z env tm = pure tm
transLoop (S k) env tm
    = do u <- newRef Upd False
         tm' <- trans env [] tm
         upd <- get Upd
         if upd -- If there was a transform applied, go around again until
                -- we hit the threshold
            then transLoop k env tm'
            else pure tm'

export
covering
applyTransforms : {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Term vars -> Core (Term vars)
applyTransforms env tm = transLoop 5 env tm
