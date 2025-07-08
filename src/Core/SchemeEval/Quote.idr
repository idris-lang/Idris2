module Core.SchemeEval.Quote

import Core.Context
import Core.Core
import Core.Env
import Core.SchemeEval.Compile
import Core.SchemeEval.Evaluate
import Core.TT

mutual
  quoteArgs : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref Sym Integer -> Bounds bound ->
              Env Term free -> List (Core (SNF free)) ->
              Core (List (Term (Scope.addInner free bound)))
  quoteArgs q bound env args
      = traverse (\arg => do arg' <- arg
                             quoteGen q bound env arg') args

  quotePi : {auto c : Ref Ctxt Defs} ->
            {bound, free : _} ->
            Ref Sym Integer -> Bounds bound ->
            Env Term free -> PiInfo (SNF free) ->
            Core (PiInfo (Term (Scope.addInner free bound)))
  quotePi q bound env Explicit = pure Explicit
  quotePi q bound env Implicit = pure Implicit
  quotePi q bound env AutoImplicit = pure AutoImplicit
  quotePi q bound env (DefImplicit t)
      = do t' <- quoteGen q bound env t
           pure (DefImplicit t')

  quoteBinder : {auto c : Ref Ctxt Defs} ->
                {bound, free : _} ->
                Ref Sym Integer -> Bounds bound ->
                Env Term free -> Binder (SNF free) ->
                Core (Binder (Term (Scope.addInner free bound)))
  quoteBinder q bound env (Lam fc r p ty)
     = do ty' <- quoteGen q bound env ty
          p' <- quotePi q bound env p
          pure (Lam fc r p' ty')
  quoteBinder q bound env (Let fc r val ty)
     = do ty' <- quoteGen q bound env ty
          val' <- quoteGen q bound env val
          pure (Let fc r val' ty')
  quoteBinder q bound env (Pi fc r p ty)
     = do ty' <- quoteGen q bound env ty
          p' <- quotePi q bound env p
          pure (Pi fc r p' ty')
  quoteBinder q bound env (PVar fc r p ty)
     = do ty' <- quoteGen q bound env ty
          p' <- quotePi q bound env p
          pure (PVar fc r p' ty')
  quoteBinder q bound env (PLet fc r val ty)
     = do ty' <- quoteGen q bound env ty
          val' <- quoteGen q bound env val
          pure (PLet fc r val' ty')
  quoteBinder q bound env (PVTy fc r ty)
     = do ty' <- quoteGen q bound env ty
          pure (PVTy fc r ty')

  quoteHead : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref Sym Integer ->
              FC -> Bounds bound -> Env Term free -> SHead free ->
              Core (Term (Scope.addInner free bound))
  quoteHead {bound} q fc bounds env (SLocal idx prf)
      = let MkVar prf' = addLater bound prf in
            pure (Local fc Nothing _ prf')
    where
      addLater : {idx : _} ->
                 (ys : Scope) -> (0 p : IsVar n idx xs) ->
                 Var (Scope.addInner xs ys)
      addLater [<] isv = MkVar isv
      addLater (xs :< x) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q fc bounds env (SRef nt n)
      = pure $ case findName bounds of
             Just (MkVar p) => Local fc Nothing _ (embedIsVar p)
             Nothing => Ref fc nt n
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x n' ns)
          = if n == n'
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
  quoteHead q fc bounds env (SMeta n i args)
      = do args' <- quoteArgs q bounds env args
           pure $ Meta fc n i args'

  quoteGen : {auto c : Ref Ctxt Defs} ->
             {bound, vars : _} ->
             Ref Sym Integer -> Bounds bound ->
             Env Term vars -> SNF vars -> Core (Term (Scope.addInner vars bound))
  quoteGen q bound env (SBind fc n b sc)
      = do i <- nextName
           let var = UN (Basic ("b-" ++ show (fromInteger i)))
           -- Ref Bound gets turned directly into a symbol by seval, which
           -- we can then read back when quoting the scope
           arg <- seval EvalAll env (Ref fc Bound var)
           sc' <- quoteGen q (Add n var bound) env !(sc arg)
           b' <- quoteBinder q bound env b
           pure (Bind fc n b' sc')
  quoteGen q bound env (SApp fc f args)
      = do f' <- quoteHead q fc bound env f
           args' <- quoteArgs q bound env args
           pure $ apply fc f' args'
  quoteGen q bound env (SDCon fc n t ar args)
      = do args' <- quoteArgs q bound env args
           pure $ apply fc (Ref fc (DataCon t ar) n) args'
  quoteGen q bound env (STCon fc n t ar args)
      = do args' <- quoteArgs q bound env args
           pure $ apply fc (Ref fc (TyCon t ar) n) args'
  quoteGen q bound env (SDelayed fc r arg)
      = do argQ <- quoteGen q bound env arg
           pure (TDelayed fc r argQ)
  quoteGen q bound env (SDelay fc r ty arg)
      = do argQ <- quoteGen q bound env !arg
           tyQ <- quoteGen q bound env !ty
           pure (TDelay fc r tyQ argQ)
  quoteGen q bound env (SForce fc r arg)
      = case arg of
             SDelay fc _ _ arg => quoteGen q bound env !arg
             _ => do arg' <- quoteGen q bound env arg
                     pure $ (TForce fc r arg')
  quoteGen q bound env (SPrimVal fc c) = pure $ PrimVal fc c
  quoteGen q bound env (SErased fc Impossible) = pure $ Erased fc Impossible
  quoteGen q bound env (SErased fc Placeholder) = pure $ Erased fc Placeholder
  quoteGen q bound env (SErased fc (Dotted t))
    = pure $ Erased fc $ Dotted !(quoteGen q bound env t)
  quoteGen q bound env (SType fc u) = pure $ TType fc u

export
quote : {auto c : Ref Ctxt Defs} ->
        {vars : _} ->
        Env Term vars -> SNF vars -> Core (Term vars)
quote env tm
    = do q <- newRef Sym 0
         quoteGen q None env tm
