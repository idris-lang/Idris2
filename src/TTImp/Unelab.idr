module TTImp.Unelab

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Value
import Core.TT

import TTImp.TTImp

import Data.List
import Data.String

%default covering

used : (idx : Nat) -> Term vars -> Bool
used idx (Local _ _ var _) = idx == var
used {vars} idx (Bind _ x b sc) = usedBinder b || used (1 + idx) sc
  where
    usedBinder : Binder (Term vars) -> Bool
    usedBinder (Let _ _ val ty) = used idx val || used idx ty
    usedBinder b = used idx (binderType b)
used idx (Meta _ _ _ args) = any (used idx) args
used idx (App _ f a) = used idx f || used idx a
used idx (As _ _ _ pat) = used idx pat
used idx (TDelayed _ _ tm) = used idx tm
used idx (TDelay _ _ _ tm) = used idx tm
used idx (TForce _ _ tm) = used idx tm
used idx _ = False

data UnelabMode
     = Full
     | NoSugar Bool -- uniqify names
     | ImplicitHoles

Eq UnelabMode where
   Full == Full = True
   NoSugar t == NoSugar u = t == u
   ImplicitHoles == ImplicitHoles = True
   _ == _ = False

mutual
  unelabCase : {auto c : Ref Ctxt Defs} ->
               List (Name, Nat) ->
               Name -> List IArg -> IRawImp ->
               Core IRawImp
  unelabCase nest n args orig
      = do defs <- get Ctxt
           Just glob <- lookupCtxtExact n (gamma defs)
                | Nothing => pure orig
           let PMDef _ pargs treect _ pats = definition glob
                | _ => pure orig
           let Just argpos = findArgPos treect
                | _ => pure orig
           if length args == length pargs
              then mkCase pats argpos 0 args
              else pure orig
    where
      -- Need to find the position of the scrutinee to rebuild original
      -- case correctly
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case idx p _ _) = Just idx
      findArgPos _ = Nothing

      idxOrDefault : Nat -> a -> List a -> a
      idxOrDefault Z def (x :: xs) = x
      idxOrDefault (S k) def (_ :: xs) = idxOrDefault k def xs
      idxOrDefault _ def [] = def

      getNth : Nat -> Term vars -> Term vars
      getNth n tm
          = case getFnArgs tm of
                 (f, as) => idxOrDefault n f as

      nthArg : FC -> Nat -> Term vars -> Term vars
      nthArg fc drop (App afc f a) = getNth drop (App afc f a)
      nthArg fc drop tm = Erased fc False

      mkClause : FC -> Nat ->
                 (vs ** (Env Term vs, Term vs, Term vs)) ->
                 Core IImpClause
      mkClause fc dropped (vs ** (env, lhs, rhs))
          = do let pat = nthArg fc dropped lhs
               logTerm "unelab.case" 20 "Unelaborating LHS" pat
               lhs' <- unelabTy Full nest env pat
               logTerm "unelab.case" 20 "Unelaborating RHS" rhs
               logEnv "unelab.case" 20 "In Env" env
               rhs' <- unelabTy Full nest env rhs
               pure (PatClause fc (fst lhs') (fst rhs'))

      mkCase : List (vs ** (Env Term vs, Term vs, Term vs)) ->
               Nat -> Nat -> List IArg -> Core IRawImp
      mkCase pats (S k) dropped (_ :: args) = mkCase pats k (S dropped) args
      mkCase pats Z dropped (Explicit fc tm :: _)
          = do pats' <- traverse (mkClause fc dropped) pats
               pure $ ICase fc tm (Implicit fc False) pats'
      mkCase _ _ _ _ = pure orig

  unelabSugar : {auto c : Ref Ctxt Defs} ->
                (umode : UnelabMode) ->
                (nest : List (Name, Nat)) ->
                (IRawImp, Glued vars) ->
                Core (IRawImp, Glued vars)
  unelabSugar (NoSugar _) nest res = pure res
  unelabSugar ImplicitHoles nest res = pure res
  unelabSugar _ nest (tm, ty)
      = let (f, args) = getFnArgs tm [] in
            case f of
             IVar fc (MkKindedName _ _ (NS ns (CaseBlock n i))) =>
               do log "unelab.case" 20 $ unlines
                         [ "Unelaborating case " ++ show (n, i)
                         , "with arguments: " ++ show args
                         ]
                  tm <- unelabCase nest (NS ns (CaseBlock n i)) args tm
                  log "unelab.case" 20 $ "Unelaborated to: " ++ show tm
                  pure (tm, ty)
             _ => pure (tm, ty)

  dropParams : {auto c : Ref Ctxt Defs} ->
               List (Name, Nat) -> (IRawImp, Glued vars) ->
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
      = unelabSugar umode nest !(dropParams nest !(unelabTy' umode nest env tm))

  unelabTy' : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              (umode : UnelabMode) ->
              (nest : List (Name, Nat)) ->
              Env Term vars -> Term vars ->
              Core (IRawImp, Glued vars)
  unelabTy' umode nest env (Local fc _ idx p)
      = do let nm = nameAt p
           log "unelab.case" 20 $ "Found local name: " ++ show nm
           let ty = gnf env (binderType (getBinder p env))
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

           pure (IVar fc (MkKindedName (Just nt) fn n'), gnf env (embed ty))
  unelabTy' umode nest env (Meta fc n i args)
      = do defs <- get Ctxt
           let mkn = nameRoot n
           Just ty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (IHole fc mkn, gErased fc)
           pure (IHole fc mkn, gnf env (embed ty))
  unelabTy' umode nest env (Bind fc x b sc)
      = do (sc', scty) <- unelabTy umode nest (b :: env) sc
           case umode of
                NoSugar True =>
                   let x' = uniqueLocal vars x in
                       unelabBinder umode nest fc env x' b
                                    (renameVars (CompatExt CompatPre) sc) sc'
                                    (renameVars (CompatExt CompatPre) !(getTerm scty))
                _ => unelabBinder umode nest fc env x b sc sc' !(getTerm scty)
    where
      next : Name -> Name
      next (MN n i) = MN n (i + 1)
      next (UN n) = MN (show n) 0
      next (NS ns n) = NS ns (next n)
      next n = MN (show n) 0

      uniqueLocal : List Name -> Name -> Name
      uniqueLocal vs n
         = if n `elem` vs
              then uniqueLocal vs (next n)
              else n
  unelabTy' umode nest env (App fc fn arg)
      = do (fn', gfnty) <- unelabTy umode nest env fn
           (arg', gargty) <- unelabTy umode nest env arg
           fnty <- getNF gfnty
           defs <- get Ctxt
           case fnty of
                NBind _ x (Pi _ rig Explicit ty) sc
                  => do sc' <- sc defs (toClosure defaultOpts env arg)
                        pure (IApp fc fn' arg',
                                glueBack defs env sc')
                NBind _ x (Pi _ rig p ty) sc
                  => do sc' <- sc defs (toClosure defaultOpts env arg)
                        pure (INamedApp fc fn' x arg',
                                glueBack defs env sc')
                _ => pure (IApp fc fn' arg', gErased fc)
  unelabTy' umode nest env (As fc s p tm)
      = do (p', _) <- unelabTy' umode nest env p
           (tm', ty) <- unelabTy' umode nest env tm
           case p' of
                IVar _ n =>
                    case umode of
                         NoSugar _ => pure (IAs fc (getLoc p) s n.rawName tm', ty)
                         _ => pure (tm', ty)
                _ => pure (tm', ty) -- Should never happen!
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
  unelabTy' umode nest env (Erased fc _) = pure (Implicit fc True, gErased fc)
  unelabTy' umode nest env (TType fc _) = pure (IType fc, gType fc (MN "top" 0))

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
                 Binder (Term vars) -> Term (x :: vars) ->
                 IRawImp -> Term (x :: vars) ->
                 Core (IRawImp, Glued vars)
  unelabBinder umode nest fc env x (Lam fc' rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode nest env ty
           p' <- unelabPi umode nest env p
           pure (ILam fc rig p' (Just x) ty' sc,
                    gnf env (Bind fc x (Pi fc' rig p ty) scty))
  unelabBinder umode nest fc env x (Let fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode nest env val
           (ty', _) <- unelabTy umode nest env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    gnf env (Bind fc x (Let fc' rig val ty) scty))
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
           pure (sc, gnf env (Bind fc x (PVTy fc' rig ty) scty))
  unelabBinder umode nest fc env x (PLet fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode nest env val
           (ty', _) <- unelabTy umode nest env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    gnf env (Bind fc x (PLet fc' rig val ty) scty))
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
             List (Name, Nat) ->
             Env Term vars ->
             Term vars -> Core IRawImp
unelabNest nest env (Meta fc n i args)
    = do let mkn = nameRoot n ++ showScope args
         pure (IHole fc mkn)
  where
    toName : Term vars -> Maybe Name
    toName (Local _ _ idx p) = Just (nameAt p)
    toName _ = Nothing

    showNScope : List Name -> String
    showNScope [] = "[no locals in scope]"
    showNScope ns = "[locals in scope: " ++ showSep ", " (map show (nub ns)) ++ "]"

    showScope : List (Term vars) -> String
    showScope ts = " " ++ showNScope (mapMaybe toName ts)

unelabNest nest env tm
    = do tm' <- unelabTy Full nest env tm
         pure $ fst tm'

export
unelab : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Env Term vars ->
         Term vars -> Core IRawImp
unelab = unelabNest []
