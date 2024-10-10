module Core.Normalise.Quote

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise.Eval
import Core.TT
import Core.Value

import Data.SnocList

%default covering

export
data QVar : Type where

public export
record QuoteOpts where
  constructor MkQuoteOpts
  topLevel : Bool -- At the top level application
  patterns : Bool -- only quote as far as is useful to get LHS patterns.
                  -- That means, stop on encountering a block function or
                  -- local
  sizeLimit : Maybe Nat

public export
interface Quote tm where
    quote : {auto c : Ref Ctxt Defs} ->
            {vars : SnocList Name} ->
            Defs -> Env Term vars -> tm vars -> Core (Term vars)
    quoteLHS : {auto c : Ref Ctxt Defs} ->
               {vars : SnocList Name} ->
               Defs -> Env Term vars -> tm vars -> Core (Term vars)
    quoteOpts : {auto c : Ref Ctxt Defs} ->
                {vars : SnocList Name} ->
                QuoteOpts -> Defs -> Env Term vars -> tm vars -> Core (Term vars)

    quoteGen : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Ref QVar Int -> QuoteOpts ->
               Defs -> Env Term vars -> tm vars -> Core (Term vars)

    quote defs env tm
        = do q <- newRef QVar 0
             logDepth $ quoteGen q (MkQuoteOpts True False Nothing) defs env tm

    quoteLHS defs env tm
        = do q <- newRef QVar 0
             logDepth $ quoteGen q (MkQuoteOpts True True Nothing) defs env tm

    quoteOpts opts defs env tm
        = do q <- newRef QVar 0
             logDepth $ quoteGen q opts defs env tm

export
genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArg : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
              Env Term free -> Closure free ->
              Core (Term (free ++ bound))
  quoteArg q opts defs bounds env a
      = quoteGenNF q opts defs bounds env !(evalClosure defs a)

  quoteArgWithFC : {auto c : Ref Ctxt Defs} ->
                   {bound, free : _} ->
                   Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
                   Env Term free -> (FC, Closure free) ->
                   Core ((FC, Term (free ++ bound)))
  quoteArgWithFC q opts defs bounds env
       = traversePair (quoteArg q opts defs bounds env)

  quoteArgs : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
              Env Term free -> List (Closure free) ->
              Core (List (Term (free ++ bound)))
  quoteArgs q opts defs bounds env = traverse (quoteArg q opts defs bounds env)

  quoteArgsWithFC : {auto c : Ref Ctxt Defs} ->
                    {bound, free : _} ->
                    Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
                    Env Term free -> SnocList (FC, Closure free) ->
                    Core (SnocList (FC, Term (free ++ bound)))
  quoteArgsWithFC q opts defs bounds env
      = traverse (quoteArgWithFC q opts defs bounds env)

  quoteHead : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> QuoteOpts -> Defs ->
              FC -> Bounds bound -> Env Term free -> NHead free ->
              Core (Term (free ++ bound))
  quoteHead {bound} q opts defs fc bounds env (NLocal mrig _ prf)
      = let MkVar prf' = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : {idx : _} ->
                 (ys : SnocList Name) -> (0 p : IsVar n idx xs) ->
                 Var (xs ++ ys)
      addLater [<] isv = MkVar isv
      addLater (xs :< x) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q opts defs fc bounds env (NRef Bound (MN n i))
      = pure $ case findName bounds of
             Just (MkVar p) => Local fc Nothing _ (embedIsVar p)
             Nothing => Ref fc Bound (MN n i)
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <-findName ns
               Just (MkVar (Later p))
  quoteHead q opts defs fc bounds env (NRef nt n) = pure $ Ref fc nt n
  quoteHead q opts defs fc bounds env (NMeta n i args)
      = do args' <- quoteArgs q opts defs bounds env args
           pure $ Meta fc n i args'

  quotePi : {auto c : Ref Ctxt Defs} ->
            {bound, free : _} ->
            Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
            Env Term free -> PiInfo (Closure free) ->
            Core (PiInfo (Term (free ++ bound)))
  quotePi q opts defs bounds env Explicit = pure Explicit
  quotePi q opts defs bounds env Implicit = pure Implicit
  quotePi q opts defs bounds env AutoImplicit = pure AutoImplicit
  quotePi q opts defs bounds env (DefImplicit t)
      = do t' <- quoteGenNF q opts defs bounds env !(evalClosure defs t)
           pure (DefImplicit t')

  quoteBinder : {auto c : Ref Ctxt Defs} ->
                {bound, free : _} ->
                Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
                Env Term free -> Binder (Closure free) ->
                Core (Binder (Term (free ++ bound)))
  quoteBinder q opts defs bounds env (Lam fc r p ty)
      = do ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           p' <- quotePi q opts defs bounds env p
           pure (Lam fc r p' ty')
  quoteBinder q opts defs bounds env (Let fc r val ty)
      = do val' <- quoteGenNF q opts defs bounds env !(evalClosure defs val)
           ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           pure (Let fc r val' ty')
  quoteBinder q opts defs bounds env (Pi fc r p ty)
      = do ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           p' <- quotePi q opts defs bounds env p
           pure (Pi fc r p' ty')
  quoteBinder q opts defs bounds env (PVar fc r p ty)
      = do ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           p' <- quotePi q opts defs bounds env p
           pure (PVar fc r p' ty')
  quoteBinder q opts defs bounds env (PLet fc r val ty)
      = do val' <- quoteGenNF q opts defs bounds env !(evalClosure defs val)
           ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           pure (PLet fc r val' ty')
  quoteBinder q opts defs bounds env (PVTy fc r ty)
      = do ty' <- quoteGenNF q opts defs bounds env !(evalClosure defs ty)
           pure (PVTy fc r ty')

  quoteGenNF : {auto c : Ref Ctxt Defs} ->
               {bound, vars : _} ->
               Ref QVar Int -> QuoteOpts ->
               Defs -> Bounds bound ->
               Env Term vars -> NF vars -> Core (Term (vars ++ bound))
  quoteGenNF q opts defs bound env (NBind fc n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q opts defs (Add n var bound) env
                       !(sc defs (toClosure defaultOpts env (Ref fc Bound var)))
           b' <- quoteBinder q opts defs bound env b
           pure (Bind fc n b' sc')
  quoteGenNF q opts defs bound env (NApp fc f args)
      = do f' <- quoteHead q opts defs fc bound env f
           opts' <- case sizeLimit opts of
                         Nothing => pure opts
                         Just Z => throw (InternalError "Size limit exceeded")
                         Just (S k) => pure ({ sizeLimit := Just k } opts)
           args' <- if patterns opts && not (topLevel opts) && isRef f
                       then do empty <- clearDefs defs
                               quoteArgsWithFC q opts' empty bound env args
                               else quoteArgsWithFC q ({ topLevel := False } opts')
                                                    defs bound env args
           pure $ applyStackWithFC f' args'
    where
      isRef : NHead vars -> Bool
      isRef (NRef{}) = True
      isRef _ = False
  quoteGenNF q opts defs bound env (NDCon fc n t ar args)
      = do args' <- quoteArgsWithFC q opts defs bound env args
           pure $ applyStackWithFC (Ref fc (DataCon t ar) n) args'
  quoteGenNF q opts defs bound env (NTCon fc n t ar args)
      = do args' <- quoteArgsWithFC q opts defs bound env args
           pure $ applyStackWithFC (Ref fc (TyCon t ar) n) args'
  quoteGenNF q opts defs bound env (NAs fc s n pat)
      = do n' <- quoteGenNF q opts defs bound env n
           pat' <- quoteGenNF q opts defs bound env pat
           pure (As fc s n' pat')
  quoteGenNF q opts defs bound env (NDelayed fc r arg)
      = do argQ <- quoteGenNF q opts defs bound env arg
           pure (TDelayed fc r argQ)
  quoteGenNF q opts defs bound env (NDelay fc r ty arg)
      = do argNF <- evalClosure defs (toHolesOnly arg)
           argQ <- quoteGenNF q opts defs bound env argNF
           tyNF <- evalClosure defs (toHolesOnly ty)
           tyQ <- quoteGenNF q opts defs bound env tyNF
           pure (TDelay fc r tyQ argQ)
    where
      toHolesOnly : Closure vs -> Closure vs
      toHolesOnly (MkClosure opts locs env tm)
          = MkClosure ({ holesOnly := True,
                         argHolesOnly := True } opts)
                      locs env tm
      toHolesOnly c = c
  quoteGenNF q opts defs bound env (NForce fc r arg args)
      = do args' <- quoteArgsWithFC q opts defs bound env args
           case arg of
                NDelay fc _ _ arg =>
                   do argNF <- evalClosure defs arg
                      pure $ applyStackWithFC !(quoteGenNF q opts defs bound env argNF) args'
                _ => do arg' <- quoteGenNF q opts defs bound env arg
                        pure $ applyStackWithFC (TForce fc r arg') args'
  quoteGenNF q opts defs bound env (NPrimVal fc c) = pure $ PrimVal fc c
  quoteGenNF q opts defs bound env (NErased fc t)
    = Erased fc <$> traverse @{%search} @{CORE} (\ nf => quoteGenNF q opts defs bound env nf) t
  quoteGenNF q opts defs bound env (NType fc u) = pure $ TType fc u

export
Quote NF where
  quoteGen q opts defs env tm = quoteGenNF q opts defs None env tm

export
Quote Term where
  quoteGen q opts defs env tm = pure tm

export
Quote Closure where
  quoteGen q opts defs env c = quoteGen q opts defs env !(evalClosure defs c)

quoteWithPiGen : {auto _ : Ref Ctxt Defs} ->
                 {bound, vars : _} ->
                 Ref QVar Int -> QuoteOpts -> Defs -> Bounds bound ->
                 Env Term vars -> NF vars -> Core (Term (vars ++ bound))
quoteWithPiGen q opts defs bound env (NBind fc n (Pi bfc c p ty) sc)
    = do var <- genName "qv"
         empty <- clearDefs defs
         sc' <- quoteWithPiGen q opts defs (Add n var bound) env
                     !(sc defs (toClosure defaultOpts env (Ref fc Bound var)))
         ty' <- quoteGenNF q opts empty bound env !(evalClosure empty ty)
         p' <- quotePi q opts empty bound env p
         pure (Bind fc n (Pi bfc c p' ty') sc')
quoteWithPiGen q opts defs bound env (NErased fc t)
  = Erased fc <$> traverse @{%search} @{CORE} (quoteWithPiGen q opts defs bound env) t
quoteWithPiGen q opts defs bound env tm
    = do empty <- clearDefs defs
         quoteGenNF q opts empty bound env tm

-- Quote back to a term, but only to find out how many Pi bindings there
-- are, don't reduce anything else
export
quoteWithPi : {auto c : Ref Ctxt Defs} ->
              {vars : SnocList Name} ->
              Defs -> Env Term vars -> NF vars -> Core (Term vars)
quoteWithPi defs env tm
    = do q <- newRef QVar 0
         quoteWithPiGen q (MkQuoteOpts True False Nothing) defs None env tm
