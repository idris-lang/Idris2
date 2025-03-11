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

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf

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

public export
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

  ||| Unelaborate a call to a case expression as an inline case.
  ||| This should allow us to eventurally resugar case blocks and if-then-else calls.
  |||
  ||| This is really hard however because all we have access to is the
  ||| clauses of the lifted case expression. So e.g.
  |||      f x = case g x of p -> e
  ||| became
  |||      f x = f-case x (g x)
  |||      f-case x p = e
  ||| and so to display the
  |||      f-case (h y) (g (p o))
  ||| correctly we need to:
  ||| 1. extract p from f-case x p
  ||| 2. replace x with (h y) in e
  |||
  ||| However it can be the case that x has been split because it was forced by a
  ||| pattern in p and so looking at (f-case x p) we may not be able to recover the
  ||| name x.
  |||
  ||| We will try to do our best...
  unelabCase : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               List (Name, Nat) ->
               Env Term vars ->
               Name ->
               Scopeable (Term vars) ->
               Core (Maybe IRawImp)
  unelabCase nest env n args
      = do defs <- get Ctxt
           Just glob <- lookupCtxtExact n (gamma defs)
                | Nothing => pure Nothing
           let PMDef _ pargs treect _ pats = definition glob
                | _ => pure Nothing
           let Just argpos = findArgPos treect
                | _ => pure Nothing
           if length args == length pargs
              then mkCase pats argpos args
              else pure Nothing
    where
      -- Need to find the position of the scrutinee to rebuild original
      -- case correctly
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case idx p _ _) = Just idx
      findArgPos _ = Nothing

      idxOrMaybe : Nat -> Scopeable a -> Maybe a
      idxOrMaybe Z (x :: _) = Just x
      idxOrMaybe (S k) (_ :: xs) = idxOrMaybe k xs
      idxOrMaybe _ [] = Nothing

      -- TODO: some utility like this should probably be implemented in Core
      substVars : Scopeable (List (Var vs), Term vs) -> Term vs -> Term vs
      substVars xs tm@(Local fc _ idx prf)
          = case find (any ((idx ==) . varIdx) . fst) xs of
                 Just (_, new) => new
                 Nothing => tm
      substVars xs (Meta fc n i args)
          = Meta fc n i (map (substVars xs) args)
      substVars xs (Bind fc y b scope)
          = Bind fc y (map (substVars xs) b) (substVars (map (bimap (map weaken) weaken) xs) scope)
      substVars xs (App fc fn arg)
          = App fc (substVars xs fn) (substVars xs arg)
      substVars xs (As fc s as pat)
          = As fc s as (substVars xs pat)
      substVars xs (TDelayed fc y z)
          = TDelayed fc y (substVars xs z)
      substVars xs (TDelay fc y t z)
          = TDelay fc y (substVars xs t) (substVars xs z)
      substVars xs (TForce fc r y)
          = TForce fc r (substVars xs y)
      substVars xs tm = tm

      substArgs : SizeOf vs -> Scopeable (List (Var vs), Term vars) -> Term vs -> Term (vs ++ vars)
      substArgs p substs tm =
        let
          substs' = map (bimap (map $ embed {outer = vars}) (weakenNs p)) substs
          tm' = embed tm
        in
          substVars substs' tm'

      argVars : {vs : _} -> Term vs -> List (Var vs)
      argVars (As _ _ as pat) = argVars as ++ argVars pat
      argVars (Local _ _ _ p) = [MkVar p]
      argVars _ = []

      mkClause : FC -> Nat ->
                 Scopeable (Term vars) ->
                 (vs ** (Env Term vs, Term vs, Term vs)) ->
                 Core (Maybe IImpClause)
      mkClause fc argpos args (vs ** (clauseEnv, lhs, rhs))
          = do logTerm "unelab.case.clause" 20 "Unelaborating clause" lhs
               let patArgs = snd (getFnArgs lhs)
                   Just pat = idxOrMaybe argpos patArgs
                     | _ => pure Nothing
                   rhs = substArgs (mkSizeOf vs) (zip (map argVars patArgs) args) rhs
               logTerm "unelab.case.clause" 20 "Unelaborating LHS" pat
               lhs' <- unelabTy Full nest clauseEnv pat
               logTerm "unelab.case.clause" 20 "Unelaborating RHS" rhs
               logEnv "unelab.case.clause" 20 "In Env" clauseEnv
               rhs' <- unelabTy Full nest (clauseEnv ++ env) rhs
               pure $ Just $ (PatClause fc (fst lhs') (fst rhs'))

      ||| mkCase looks up the value passed as the scrutinee of the case-block.
      ||| @ argpos  is the index of the case-block's scrutinee in args
      ||| @ args    is the list of arguments at the call site of the case-block
      |||
      ||| Once we have the scrutinee `e`, we can form `case e of` and so focus
      ||| on manufacturing the clauses.
      mkCase : List (vs ** (Env Term vs, Term vs, Term vs)) ->
               (argpos : Nat) -> Scopeable (Term vars) -> Core (Maybe IRawImp)
      mkCase pats argpos args
          = do unless (null args) $ log "unelab.case.clause" 20 $
                 unwords $ "Ignoring" :: map show (toList args)
               let Just scrutinee = idxOrMaybe argpos args
                     | _ => pure Nothing
                   fc = getLoc scrutinee
               (tm, _) <- unelabTy Full nest env scrutinee
               Just pats' <- map sequence $ traverse (mkClause fc argpos args) pats
                 | _ => pure Nothing
               -- TODO: actually grab the fnopts?
               pure $ Just $ ICase fc [] tm (Implicit fc False) pats'

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
           def <- lookupDefExact (Resolved i) (gamma defs)
           let term = case def of
                              (Just (BySearch _ d _)) => ISearch fc d
                              _ => IHole fc mkn
           Just ty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => case umode of
                                 ImplicitHoles => pure (Implicit fc True, gErased fc)
                                 _ => pure (term, gErased fc)
           pure (term, gnf env (embed ty))
  unelabTy' umode nest env (Bind fc x b sc)
      = case umode of
          NoSugar True => do
            let x' = uniqueLocal vars x
            let sc : Term (x' :: vars) = compat sc
            (sc', scty) <- unelabTy umode nest (b :: env) sc
            unelabBinder umode nest fc env x' b
                         (compat sc) sc'
                         (compat !(getTerm scty))
          _ => do
            (sc', scty) <- unelabTy umode nest (b :: env) sc
            unelabBinder umode nest fc env x b sc sc' !(getTerm scty)
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
  unelabTy' umode nest env tm@(App fc fn arg)
      = do (fn', gfnty) <- unelabTy umode nest env fn
           (arg', gargty) <- unelabTy umode nest env arg
           fnty <- getNF gfnty
           defs <- get Ctxt
           Nothing <-
              case umode of
                (NoSugar _) => pure Nothing
                ImplicitHoles => pure Nothing
                _ => case getFnArgs tm of
                     (Ref _ _ fnName, args) => do
                       fullName <- getFullName fnName
                       let (NS ns (CaseBlock n i)) = fullName
                         | _ => pure Nothing
                       unelabCase nest env fullName args
                     _ => pure Nothing
             | Just tm => pure (tm, gErased fc)
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
  unelabTy' umode nest env (Erased fc (Dotted t))
    = unelabTy' umode nest env t
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
             UnelabMode ->
             List (Name, Nat) ->
             Env Term vars ->
             Term vars -> Core IRawImp
unelabNest mode nest env (Meta fc n i args)
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

unelabNest mode nest env tm
    = do tm' <- unelabTy mode nest env tm
         pure $ fst tm'

export
unelab : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         Env Term vars ->
         Term vars -> Core IRawImp
unelab = unelabNest Full []
