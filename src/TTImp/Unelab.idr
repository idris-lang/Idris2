module TTImp.Unelab

import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Options
import Core.Value
import Core.TT

import TTImp.TTImp
import TTImp.Utils

import Data.List
import Data.Strings

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

data IArg
   = Exp FC RawImp
   | Auto FC RawImp
   | Named FC Name RawImp

unIArg : IArg -> RawImp
unIArg (Exp _ t) = t
unIArg (Auto _ t) = t
unIArg (Named _ _ t) = t

Show IArg where
  show (Exp fc t) = show t
  show (Auto fc t) = "@{" ++ show t ++ "}"
  show (Named fc n t) = "{" ++ show n ++ " = " ++ show t ++ "}"

getFnArgs : RawImp -> List IArg -> (RawImp, List IArg)
getFnArgs (IApp fc f arg) args = getFnArgs f (Exp fc arg :: args)
getFnArgs (INamedApp fc f n arg) args = getFnArgs f (Named fc n arg :: args)
getFnArgs (IAutoApp fc f arg) args = getFnArgs f (Auto fc arg :: args)
getFnArgs tm args = (tm, args)

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
               Name -> List IArg -> RawImp ->
               Core RawImp
  unelabCase n args orig
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
                 Core ImpClause
      mkClause fc dropped (vs ** (env, lhs, rhs))
          = do let pat = nthArg fc dropped lhs
               logTerm "unelab.case" 20 "Unelaborating LHS" pat
               lhs' <- unelabTy Full env pat
               logTerm "unelab.case" 20 "Unelaborating RHS" rhs
               logEnv "unelab.case" 20 "In Env" env
               rhs' <- unelabTy Full env rhs
               pure (PatClause fc (fst lhs') (fst rhs'))

      mkCase : List (vs ** (Env Term vs, Term vs, Term vs)) ->
               Nat -> Nat -> List IArg -> Core RawImp
      mkCase pats (S k) dropped (_ :: args) = mkCase pats k (S dropped) args
      mkCase pats Z dropped (Exp fc tm :: _)
          = do pats' <- traverse (mkClause fc dropped) pats
               pure $ ICase fc tm (Implicit fc False) pats'
      mkCase _ _ _ _ = pure orig

  unelabSugar : {auto c : Ref Ctxt Defs} ->
                (umode : UnelabMode) ->
                (RawImp, Glued vars) ->
                Core (RawImp, Glued vars)
  unelabSugar (NoSugar _) res = pure res
  unelabSugar ImplicitHoles res = pure res
  unelabSugar _ (tm, ty)
      = let (f, args) = getFnArgs tm [] in
            case f of
             IVar fc (NS ns (CaseBlock n i)) =>
               do log "unelab.case" 20 $ unlines
                         [ "Unelaborating case " ++ show (n, i)
                         , "with arguments: " ++ show args
                         ]
                  tm <- unelabCase (NS ns (CaseBlock n i)) args tm
                  log "unelab.case" 20 $ "Unelaborated to: " ++ show tm
                  pure (tm, ty)
             _ => pure (tm, ty)

  -- Turn a term back into an unannotated TTImp. Returns the type of the
  -- unelaborated term so that we can work out where to put the implicit
  -- applications
  -- NOTE: There is *no guarantee* that this will elaborate back successfully!
  -- It's only intended for display
  unelabTy : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             Env Term vars -> Term vars ->
             Core (RawImp, Glued vars)
  unelabTy umode env tm
      = unelabSugar umode !(unelabTy' umode env tm)

  unelabTy' : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              (umode : UnelabMode) ->
              Env Term vars -> Term vars ->
              Core (RawImp, Glued vars)
  unelabTy' umode env (Local fc _ idx p)
      = do let nm = nameAt p
           log "unelab.case" 20 $ "Found local name: " ++ show nm
           let ty = gnf env (binderType (getBinder p env))
           pure (IVar fc nm, ty)
  unelabTy' umode env (Ref fc nt n)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact n (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (IVar fc n, gErased fc)
           n' <- case umode of
                      NoSugar _ => getFullName n
                      _ => aliasName !(getFullName n)
           pure (IVar fc n', gnf env (embed ty))
  unelabTy' umode env (Meta fc n i args)
      = do defs <- get Ctxt
           let mkn = nameRoot n
           Just ty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (IHole fc mkn, gErased fc)
           pure (IHole fc mkn, gnf env (embed ty))
  unelabTy' umode env (Bind fc x b sc)
      = do (sc', scty) <- unelabTy umode (b :: env) sc
           case umode of
                NoSugar True =>
                   let x' = uniqueLocal vars x in
                       unelabBinder umode fc env x' b
                                    (renameVars (CompatExt CompatPre) sc) sc'
                                    (renameVars (CompatExt CompatPre) !(getTerm scty))
                _ => unelabBinder umode fc env x b sc sc' !(getTerm scty)
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
  unelabTy' umode env (App fc fn arg)
      = do (fn', gfnty) <- unelabTy umode env fn
           (arg', gargty) <- unelabTy umode env arg
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
  unelabTy' umode env (As fc s p tm)
      = do (p', _) <- unelabTy' umode env p
           (tm', ty) <- unelabTy' umode env tm
           case p' of
                IVar _ n =>
                    case umode of
                         NoSugar _ => pure (IAs fc (getLoc p) s n tm', ty)
                         _ => pure (tm', ty)
                _ => pure (tm', ty) -- Should never happen!
  unelabTy' umode env (TDelayed fc r tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IDelayed fc r tm', gErased fc)
  unelabTy' umode env (TDelay fc r _ tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IDelay fc tm', gErased fc)
  unelabTy' umode env (TForce fc r tm)
      = do (tm', ty) <- unelabTy' umode env tm
           defs <- get Ctxt
           pure (IForce fc tm', gErased fc)
  unelabTy' umode env (PrimVal fc c) = pure (IPrimVal fc c, gErased fc)
  unelabTy' umode env (Erased fc _) = pure (Implicit fc True, gErased fc)
  unelabTy' umode env (TType fc) = pure (IType fc, gType fc)
  unelabTy' umode _ tm
      = let fc = getLoc tm in
            pure (Implicit fc False, gErased fc)

  unelabPi : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             Env Term vars -> PiInfo (Term vars) ->
             Core (PiInfo RawImp)
  unelabPi umode env Explicit = pure Explicit
  unelabPi umode env Implicit = pure Implicit
  unelabPi umode env AutoImplicit = pure AutoImplicit
  unelabPi umode env (DefImplicit t)
      = do (t', _) <- unelabTy umode env t
           pure (DefImplicit t')

  unelabBinder : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 (umode : UnelabMode) ->
                 FC -> Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (x :: vars) ->
                 RawImp -> Term (x :: vars) ->
                 Core (RawImp, Glued vars)
  unelabBinder umode fc env x (Lam fc' rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           p' <- unelabPi umode env p
           pure (ILam fc rig p' (Just x) ty' sc,
                    gnf env (Bind fc x (Pi fc' rig p ty) scty))
  unelabBinder umode fc env x (Let fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode env val
           (ty', _) <- unelabTy umode env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    gnf env (Bind fc x (Let fc' rig val ty) scty))
  unelabBinder umode fc env x (Pi _ rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           p' <- unelabPi umode env p
           let nm = if used 0 sctm || isNoSugar umode
                       then Just x
                       else if rig /= top || isDefImp p
                               then Just (UN "_")
                               else Nothing
           pure (IPi fc rig p' nm ty' sc, gType fc)
    where
      isNoSugar : UnelabMode -> Bool
      isNoSugar (NoSugar _) = True
      isNoSugar _ = False
      isDefImp : PiInfo t -> Bool
      isDefImp (DefImplicit _) = True
      isDefImp _ = False
  unelabBinder umode fc env x (PVar fc' rig _ ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           pure (sc, gnf env (Bind fc x (PVTy fc' rig ty) scty))
  unelabBinder umode fc env x (PLet fc' rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode env val
           (ty', _) <- unelabTy umode env ty
           pure (ILet fc EmptyFC rig x ty' val' sc,
                    gnf env (Bind fc x (PLet fc' rig val ty) scty))
  unelabBinder umode fc env x (PVTy _ rig ty) sctm sc scty
      = do (ty', _) <- unelabTy umode env ty
           pure (sc, gType fc)

export
unelabNoSugar : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars -> Core RawImp
unelabNoSugar env tm
    = do tm' <- unelabTy (NoSugar False) env tm
         pure $ fst tm'

export
unelabUniqueBinders : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars -> Core RawImp
unelabUniqueBinders env tm
    = do tm' <- unelabTy (NoSugar True) env tm
         pure $ fst tm'

export
unelabNoPatvars : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Term vars -> Core RawImp
unelabNoPatvars env tm
    = do tm' <- unelabTy ImplicitHoles env tm
         pure $ fst tm'

export
unelab : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Env Term vars -> Term vars -> Core RawImp
unelab env (Meta fc n i args)
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

unelab env tm
    = do tm' <- unelabTy Full env tm
         pure $ fst tm'
