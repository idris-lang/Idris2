module TTImp.Unelab

import Core.Context.Log
import Core.Env

import TTImp.TTImp

import Data.String
import Data.Vect

import Core.Evaluate.Value
import Core.Evaluate.Quote
import Core.Evaluate.Normalise
import Core.Evaluate.Convert
import Core.Evaluate.Expand
import Core.Evaluate
import Core.Name.CompatibleVars

import Libraries.Data.VarSet
import Libraries.Data.SnocList.SizeOf

%default covering

used : (idx : Nat) -> Term vars -> Bool
used idx (Local _ _ var _) = idx == var
used {vars} idx (Bind _ x b sc) = usedBinder b || used (1 + idx) sc
  where
    usedBinder : Binder (Term vars) -> Bool
    usedBinder (Let _ _ val ty) = used idx val || used idx ty
    usedBinder b = used idx (binderType b)
used idx (Meta _ _ _ args) = any (used idx . snd) args
used idx (App _ f _ a) = used idx f || used idx a
used idx (As _ _ _ pat) = used idx pat
used idx (TDelayed _ _ tm) = used idx tm
used idx (TDelay _ _ _ tm) = used idx tm
used idx (TForce _ _ tm) = used idx tm
used idx (PrimOp _ _ args) = any (used idx) args
used idx _ = False

public export
data UnelabMode
     = Full
     | NoSugar Bool -- uniqify names
     | ImplicitHoles
     | NoImplicits

Eq UnelabMode where
   Full == Full = True
   NoSugar t == NoSugar u = t == u
   ImplicitHoles == ImplicitHoles = True
   NoImplicits == NoImplicits = True
   _ == _ = False

mutual
  dropParams : List (Name, Nat) -> (IRawImp, Glued vars) ->
               Core (IRawImp, Glued vars)
  dropParams nest (tm, ty)
     = case getFnArgs tm [] of
            (IVar fc n, args) =>
                case lookup (rawName n) nest of
                     Nothing => pure (tm, ty)
                     Just i => pure $ (apply (IVar fc n) (drop i args), ty)
            _ => pure (tm, ty)
    where
      apply : IRawImp -> List IArg -> IRawImp
      apply tm [] = tm
      apply tm (Explicit fc a :: args) = apply (IApp fc tm a) args
      apply tm (Auto fc a :: args) = apply (IAutoApp fc tm a) args
      apply tm (Named fc n a :: args) = apply (INamedApp fc tm n a) args

  -- Turn a term back into an unannotated TTImp. Returns the type of the
  -- unelaborated term so that we can work out where to put the implicit
  -- applications
  -- NOTE: There is *no guarantee* that this will elaborate back successfully!
  -- It's only intended for display
  unelabTy : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             (nest : List (Name, Nat)) ->
             Env Term vars -> Term vars ->
             Core (IRawImp, Glued vars)
  unelabTy umode nest env tm
      = dropParams nest !(unelabTy' umode nest env tm)

  unelabTy' : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              (umode : UnelabMode) ->
              (nest : List (Name, Nat)) ->
              Env Term vars -> Term vars ->
              Core (IRawImp, Glued vars)
  unelabTy' umode nest env (Local fc _ idx p)
      = do let nm = nameAt p
           log "unelab.case" 20 $ "Found local name: " ++ show nm
           ty <- nf env (binderType (getBinder p env))
           pure (IVar fc (MkKindedName (Just Bound) nm nm), ty)
  unelabTy' umode nest env (Ref fc nt n)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact n (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (IVar fc (MkKindedName (Just nt) n n), gErased fc)
           fn <- getFullName n
           n' <- case umode of
                      NoSugar _ => pure fn
                      _ => aliasName fn
           log "unelab.var" 50 $
             unwords [ "Found name:", show n
                     , " (aka " ++ show fn ++ ")"
                     , "sugared to", show n'
                     ]

           pure (IVar fc (MkKindedName (Just nt) fn n'), !(nf env (embed ty)))
  unelabTy' umode nest env (Meta fc n i args)
      = do defs <- get Ctxt
           let mkn = nameRoot n
           def <- lookupDefExact (Resolved i) (gamma defs)
           let term = case def of
                              (Just (BySearch _ d _)) => ISearch fc d
                              _ => IHole fc mkn
           Just ty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (term, gErased fc)
           pure (term, !(nf env (embed ty)))

  unelabTy' umode nest env (Bind fc x b sc)
      = case umode of
          NoSugar True => do
            let x' = uniqueLocal vars x
            let sc : Term (vars :< x') = compat sc
            let env' = Env.bind env b
            (sc', scty) <- unelabTy umode nest env' sc
            unelabBinder umode nest fc env x' b
                         (compat sc) sc'
                         (compat !(quote env' scty))
          _ => do
            let env' = Env.bind env b
            (sc', scty) <- unelabTy umode nest env' sc
            unelabBinder umode nest fc env x b sc sc' !(quote env' scty)
    where
      next : Name -> Name
      next (MN n i) = MN n (i + 1)
      next (UN n) = MN (show n) 0
      next (NS ns n) = NS ns (next n)
      next n = MN (show n) 0

      uniqueLocal : Scope -> Name -> Name
      uniqueLocal vs n
         = if n `elem` vs
              then uniqueLocal vs (next n)
              else n
  unelabTy' umode nest env tm@(App fc fn c arg)
      = do (fn', gfnty) <- unelabTy umode nest env fn
           (arg', gargty) <- unelabTy umode nest env arg
           fnty <- expand gfnty
           case fnty of
                VBind _ x (Pi _ rig Explicit ty) sc
                  => do sc' <- sc (nf env arg)
                        pure (IApp fc fn' arg', sc')
                VBind _ x (Pi _ rig p ty) sc
                  => do sc' <- sc (nf env arg)
                        case umode of
                             NoImplicits => pure (fn', sc')
                             _ => pure (INamedApp fc fn' x arg', sc')
                _ => pure (IApp fc fn' arg', VErased fc Placeholder)
  unelabTy' umode nest env (As fc s p tm)
      = do (p', _) <- unelabTy' umode nest env p
           (tm', ty) <- unelabTy' umode nest env tm
           case p' of
                IVar _ n =>
                    case umode of
                         NoSugar _ => pure (IAs fc (getLoc p) s n.rawName tm', ty)
                         _ => pure (tm', ty)
                _ => pure (tm', ty) -- Should never happen!
  unelabTy' umode nest env (Case fc ty c sc scty alts)
      = do (sc', _) <- unelabTy' umode nest env sc
           (scty', _) <- unelabTy' umode nest env scty
           alts' <- traverse unelabAlt alts
           pure (ICase fc [] sc' scty' alts', gErased fc)
    where
      unelabScope : {vars : _} ->
                    FC -> Name -> SnocList (Maybe Name, Name) ->
                    Env Term vars -> NF [<] ->
                    CaseScope vars -> Core IImpClause
      unelabScope fc n args env _ (RHS _ tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               let n' = MkKindedName (Just Bound) n n
               pure (PatClause fc (applySpine (IVar fc n') args) tm')
        where
          applySpine : IRawImp -> SnocList (Maybe Name, Name) -> IRawImp
          applySpine fn [<] = fn
          applySpine fn (args :< (Nothing, arg))
              = let arg' = MkKindedName (Just Bound) arg arg in
                    IApp fc (applySpine fn args) (IVar fc arg')
          applySpine fn (args :< (Just n, arg))
              = let arg' = MkKindedName (Just Bound) arg arg in
                    case umode of
                        ImplicitHoles => applySpine fn args
                        _ => INamedApp fc (applySpine fn args) n (IVar fc arg')

      unelabScope fc n args env (VBind _ v (Pi _ rig p ty) tsc) (Arg c x sc)
          = do p' <- the (Core (PiInfo (Term [<]))) $ case p of
                          Explicit => pure Explicit
                          Implicit => pure Implicit
                          AutoImplicit => pure AutoImplicit
                          DefImplicit t => pure $ DefImplicit !(quote [<] t)
               vty <- quote [<] ty
               let env' = env :< PVar fc rig (map embed p') (embed vty)
               -- We only need the type to make sure we're getting the plicities
               -- right, so use an explicit name to feed to the scope type
               tsc' <- expand !(tsc (pure (vRef fc Bound n)))
               let xn = case p' of
                             Explicit => Nothing
                             _ => Just v
               unelabScope fc n (args :< (xn, x)) env' tsc' sc
      unelabScope fc n args env ty (Arg c x sc)
          = do let env' = env :< PVar fc top Explicit (Erased fc Placeholder)
               unelabScope fc n (args :< (Nothing, x)) env' (VErased fc Placeholder) sc

      unelabAlt : CaseAlt vars -> Core IImpClause
      unelabAlt (ConCase fc n t sc)
          = do defs <- get Ctxt
               nty <- lookupTyExact n (gamma defs)
               let ty = case nty of
                             Nothing => Erased fc Placeholder
                             Just t => t
               unelabScope fc !(getFullName n) [<] env !(expand !(nf [<] ty)) sc
      unelabAlt (DelayCase fc t a tm)
          = do let env' = env :<
                       PVar fc top Explicit (Erased fc Placeholder) :<
                       PVar fc erased Implicit (Erased fc Placeholder)
               (tm', _) <- unelabTy' umode nest env' tm
               let a' = MkKindedName (Just Bound) a a
               pure (PatClause fc (IDelay fc (IVar fc a')) tm')
      unelabAlt (ConstCase fc c tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               pure (PatClause fc (IPrimVal fc c) tm')
      unelabAlt (DefaultCase fc tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               pure (PatClause fc (Implicit fc False) tm')

  unelabTy' umode nest env (TDelayed fc r tm)
      = do (tm', ty) <- unelabTy' umode nest env tm
           defs <- get Ctxt
           pure (IDelayed fc r tm', gErased fc)
  unelabTy' umode nest env (TDelay fc r _ tm)
      = do (tm', ty) <- unelabTy' umode nest env tm
           defs <- get Ctxt
           pure (IDelay fc tm', gErased fc)
  unelabTy' umode nest env (TForce fc r tm)
      = do (tm', ty) <- unelabTy' umode nest env tm
           defs <- get Ctxt
           pure (IForce fc tm', gErased fc)
  unelabTy' umode nest env (PrimVal fc c) = pure (IPrimVal fc c, gErased fc)
  unelabTy' umode nest env (PrimOp fc fn args)
      = -- If we ever see this in output, we've overevaluated
        pure (Implicit fc True, gErased fc)
  unelabTy' umode nest env (Erased fc (Dotted t))
    = unelabTy' umode nest env t
  unelabTy' umode nest env (Erased fc _) = pure (Implicit fc True, gErased fc)
  unelabTy' umode nest env (TType fc _) = pure (IType fc, gType fc (MN "top" 0))
  unelabTy' umode nest env (Unmatched fc msg) = pure (Implicit fc True, gUnmatched fc msg)

  unelabPi : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             (nest : List (Name, Nat)) ->
             Env Term vars -> PiInfo (Term vars) ->
             Core (PiInfo IRawImp)
  unelabPi umode nest env Explicit = pure Explicit
  unelabPi umode nest env Implicit = pure Implicit
  unelabPi umode nest env AutoImplicit = pure AutoImplicit
  unelabPi umode nest env (DefImplicit t)
      = do (t', _) <- unelabTy umode nest env t
           pure (DefImplicit t')

  unelabBinder : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 (umode : UnelabMode) ->
                 (nest : List (Name, Nat)) ->
                 FC -> Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (Scope.bind vars x) ->
                 IRawImp -> Term (Scope.bind vars x) ->
                 Core (IRawImp, Glued vars)
  unelabBinder umode nest fc env x (Lam fc' rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode nest env ty
           p' <- unelabPi umode nest env p
           pure (ILam fc rig p' (Just x) ty' sc,
                    !(nf env (Bind fc x (Pi fc' rig p ty) scty)))
  unelabBinder umode nest fc env x (Let fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode nest env val
           (ty', _) <- unelabTy umode nest env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    !(nf env (Bind fc x (Let fc' rig val ty) scty)))
  unelabBinder umode nest fc env x (Pi _ rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode nest env ty
           p' <- unelabPi umode nest env p
           let nm = if used 0 sctm || isNoSugar umode
                       then Just x
                       else if rig /= top || isDefImp p
                               then Just (UN Underscore)
                               else Nothing
           pure (IPi fc rig p' nm ty' sc, gType fc (MN "top" 0))
    where
      isNoSugar : UnelabMode -> Bool
      isNoSugar (NoSugar _) = True
      isNoSugar _ = False
      isDefImp : PiInfo t -> Bool
      isDefImp (DefImplicit _) = True
      isDefImp _ = False
  unelabBinder umode nest fc env x (PVar fc' rig _ ty) sctm sc scty
      = do (ty', _) <- unelabTy umode nest env ty
           pure (sc, !(nf env (Bind fc x (PVTy fc' rig ty) scty)))
  unelabBinder umode nest fc env x (PLet fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode nest env val
           (ty', _) <- unelabTy umode nest env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    !(nf env (Bind fc x (PLet fc' rig val ty) scty)))
  unelabBinder umode nest fc env x (PVTy _ rig ty) sctm sc scty
      = do (ty', _) <- unelabTy umode nest env ty
           pure (sc, gType fc (MN "top" 0))

export
unelabNoSugar : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars -> Core IRawImp
unelabNoSugar env tm
    = do tm' <- unelabTy (NoSugar False) [] env tm
         pure $ fst tm'

export
unelabUniqueBinders : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars -> Core IRawImp
unelabUniqueBinders env tm
    = do tm' <- unelabTy (NoSugar True) [] env tm
         pure $ fst tm'

export
unelabNoPatvars : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Term vars -> Core IRawImp
unelabNoPatvars env tm
    = do tm' <- unelabTy ImplicitHoles [] env tm
         pure $ fst tm'

export
unelabNest : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             UnelabMode ->
             List (Name, Nat) ->
             Env Term vars ->
             Term vars -> Core IRawImp
unelabNest mode nest env (Meta fc n i args)
    = do let mkn = nameRoot n ++ ((showScope $ map snd args))
         pure (IHole fc mkn)
  where
    toName : Term vars -> Maybe Name
    toName (Local _ _ idx p) = Just (nameAt p)
    toName _ = Nothing

    showNScope : List Name -> String
    showNScope [] = "[no locals in scope]"
    showNScope ns = "[locals in scope: " ++ joinBy ", " (map show (nub ns)) ++ "]"

    showScope : List (Term vars) -> String
    showScope ts = " " ++ showNScope (mapMaybe toName ts)

unelabNest mode nest env tm
    = do tm' <- unelabTy mode nest env tm
         pure $ fst tm'

export
unelab : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Env Term vars ->
         Term vars -> Core IRawImp
unelab = unelabNest Full []
