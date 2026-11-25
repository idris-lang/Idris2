module TTImp.Unelab

import Core.Context.Log
import Core.Env
import Core.UnifyState

import TTImp.TTImp

import Data.SnocList.Elem
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

mutual
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
  used idx (Case _ _ _ sc scty alts)
      = used idx sc || used idx scty || any (usedCaseAlt idx) alts
  used idx (TDelayed _ _ tm) = used idx tm
  used idx (TDelay _ _ _ tm) = used idx tm
  used idx (TForce _ _ tm) = used idx tm
  used idx (PrimOp _ _ args) = any (used idx) args
  used idx _ = False

  usedCaseScope : (idx : Nat) -> CaseScope vars -> Bool
  usedCaseScope idx (RHS fs tm)
      = any (\ (v, t) => idx == varIdx v || used idx t) fs || used idx tm
  usedCaseScope idx (Arg _ _ sc)
      = usedCaseScope (1 + idx) sc

  usedCaseAlt : (idx : Nat) -> CaseAlt vars -> Bool
  usedCaseAlt idx (ConCase _ _ _ sc)
      = usedCaseScope idx sc
  usedCaseAlt idx (DelayCase _ _ _ tm)
      = used (2 + idx) tm
  usedCaseAlt idx (ConstCase _ _ tm)
      = used idx tm
  usedCaseAlt idx (DefaultCase _ tm)
      = used idx tm

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

caseBlockPats : {auto c : Ref Ctxt Defs} ->
                Name -> Core (Maybe (Nat, List Clause))
caseBlockPats n
    = do fullName <- getFullName n
         let NS _ (CaseBlock _ _) = fullName
              | _ => pure Nothing
         defs <- get Ctxt
         Just glob <- lookupCtxtExact fullName (gamma defs)
              | Nothing => pure Nothing
         let Function _ treect _ (Just pats) = definition glob
              | _ => pure Nothing
         let Just argpos = findCaseArgPos treect
              | Nothing => pure Nothing
         pure $ Just (argpos, pats)
      where
        -- The compile-time definition is wrapped in lambdas. The first Case
        -- selects the scrutinee by its de Bruijn index.
        findCaseArgPos : Term vs -> Maybe Nat
        findCaseArgPos (Bind _ _ (Lam {}) sc)
            = findCaseArgPos sc
        findCaseArgPos (Case _ _ _ (Local _ _ idx _) _ _)
            = Just idx
        findCaseArgPos _
            = Nothing

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

  ||| Unelaborate a call to a case expression as an inline case,
  ||| using the original clauses stored in the case block definition.
  unelabCase : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               List (Name, Nat) ->
               Env Term vars ->
               Term vars ->
               Core (Maybe IRawImp)
  unelabCase nest env tm
      = case getFnArgsSpine tm of
             (Ref _ _ n, args) => do
               Just (argpos, pats) <- caseBlockPats n
                    | Nothing => pure Nothing
               let Just nargs = clauseArity pats
                    | _ => pure Nothing
               if length args == nargs
                  then mkCase pats argpos (map snd args)
                  else pure Nothing
             _ => pure Nothing
    where
      -- All clauses of a case block have the same LHS arity.
      clauseArity : List Clause -> Maybe Nat
      clauseArity []
          = Nothing
      clauseArity (MkClause _ lhs _ :: _)
          = Just $ length $ snd $ getFnArgsSpine lhs

      argVars : {0 vs : _} -> VarSet vs -> Term vs -> VarSet vs
      argVars acc (As _ _ as pat)
          = argVars (argVars acc as) pat
      argVars acc (Local _ _ _ p)
          = VarSet.insert (MkVar p) acc
      argVars acc _
          = acc

      mkClause : FC -> Nat -> SnocList (Term vars) ->
                 Clause -> Core (Maybe IImpClause)
      mkClause fc argpos args (MkClause {vars = vs'} clauseEnv lhs rhs)
          = do logTerm "unelab.case.clause" 20
                       "Unelaborating clause" lhs

               let patArgs = snd (getFnArgsSpine lhs)
                   Just (_, pat) = map fst (indexElem argpos patArgs)
                     | _ => pure Nothing
                   substs = zip (map (argVars (VarSet.empty {vs = vs'}))
                                     (map snd patArgs))
                                args
                   rhs' = substArgs (mkSizeOf vs') substs rhs

               logTerm "unelab.case.clause" 20
                       "Unelaborating LHS" pat
               lhs' <- unelabTy Full nest clauseEnv pat

               logTerm "unelab.case.clause" 20
                       "Unelaborating RHS" rhs'
               logEnv "unelab.case.clause" 20
                      "In Env" clauseEnv

               rhs'' <- unelabTy Full nest
                                 (clauseEnv ++ env)
                                 rhs'

               pure $ Just $
                 PatClause fc (fst lhs') (fst rhs'')
           where
             weakenSubsts : SnocList (VarSet vs, Term vs) ->
                            SnocList (VarSet (vs :< x), Term (vs :< x))
             weakenSubsts = map (bimap (weaken {tm = VarSet}) weaken)

             mutual
               substVars : SnocList (VarSet vs, Term vs) -> Term vs -> Term vs
               substVars xs tm@(Local fc _ idx prf)
                   = case find ((MkVar prf `VarSet.elem`) . fst) xs of
                          Just (_, new) => new
                          Nothing => tm
               substVars xs (Meta fc n i args)
                   = Meta fc n i (mapSnd @{Compose} (substVars xs) args)
               substVars xs (Bind fc y b scope)
                   = Bind fc y (map (substVars xs) b) (substVars (weakenSubsts xs) scope)
               substVars xs (App fc fn r arg)
                   = App fc (substVars xs fn) r (substVars xs arg)
               substVars xs (As fc s as pat)
                   = As fc s (substVars xs as) (substVars xs pat)
               substVars xs (Case fc ct c sc scty alts)
                   = Case fc ct c (substVars xs sc) (substVars xs scty)
                          (map (substCaseAlt xs) alts)
               substVars xs (TDelayed fc y z)
                   = TDelayed fc y (substVars xs z)
               substVars xs (TDelay fc y t z)
                   = TDelay fc y (substVars xs t) (substVars xs z)
               substVars xs (TForce fc r y)
                   = TForce fc r (substVars xs y)
               substVars xs (PrimOp fc fn args)
                   = PrimOp fc fn (map (substVars xs) args)
               substVars xs (Erased fc why)
                   = Erased fc (map (substVars xs) why)
               substVars xs tm = tm

               substCaseScope : SnocList (VarSet vs, Term vs) ->
                                CaseScope vs -> CaseScope vs
               substCaseScope xs (RHS fs tm)
                   = RHS (map (mapSnd (substVars xs)) fs) (substVars xs tm)
               substCaseScope xs (Arg c x sc)
                   = Arg c x (substCaseScope (weakenSubsts xs) sc)

               substCaseAlt : SnocList (VarSet vs, Term vs) ->
                              CaseAlt vs -> CaseAlt vs
               substCaseAlt xs (ConCase fc n t sc)
                   = ConCase fc n t (substCaseScope xs sc)
               substCaseAlt xs (DelayCase fc ty arg rhs)
                   = DelayCase fc ty arg (substVars (weakenSubsts (weakenSubsts xs)) rhs)
               substCaseAlt xs (ConstCase fc c tm)
                   = ConstCase fc c (substVars xs tm)
               substCaseAlt xs (DefaultCase fc tm)
                   = DefaultCase fc (substVars xs tm)

             substArgs : SizeOf vs -> SnocList (VarSet vs, Term vars) ->
                         Term vs -> Term (Scope.addInner vars vs)
             substArgs p substs tm
                 = let substs' =
                         map (bimap (embed {tm = VarSet} {outer = vars})
                                    (weakenNs p))
                             substs
                       tm' = embed tm
                   in substVars substs' tm'

      mkCase : List Clause -> Nat -> SnocList (Term vars) ->
               Core (Maybe IRawImp)
      mkCase pats argpos args
          = do unless (null args) $
                 log "unelab.case.clause" 20 $
                   unwords $
                     "Ignoring" :: map show (toList args)

               let Just scrutinee = map fst (indexElem argpos args)
                     | _ => pure Nothing
                   fc = getLoc scrutinee

               (scrutinee', _) <-
                 unelabTy Full nest env scrutinee

               Just clauses <-
                 map sequence $
                   traverse (mkClause fc argpos args) pats
                 | _ => pure Nothing

               pure $ Just $
                 ICase fc [] scrutinee'
                       (Implicit fc False)
                       clauses

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
           Nothing <- the (Core (Maybe IRawImp)) $
              case umode of
                Full => unelabCase nest env tm
                _ => pure Nothing
             | Just caseTm => pure (caseTm, gErased fc)
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
      = do (defaultPat, restored) <-
             case umode of
                  Full => do
                    -- Source-like output recovers default-pattern names and
                    -- uses the original clauses of generated case blocks.
                    (defaultName, restored) <-
                      the (Core (Maybe Name, Maybe IRawImp)) $
                        case ty of
                            -- A case block name lets us look up its
                            -- original clauses.
                           CaseBlock n => do
                             restored <-
                               -- Rebuild the call so that unelabCase can recover
                               -- source patterns instead of generated case variables.
                               unelabCase nest env $
                                 applyToFull fc (Ref fc Func n) env
                             defaultName <-
                               if any isDefault alts
                                  then defaultPatternName n
                                  -- Without a default alternative there is no name to recover.
                                  else pure Nothing
                             pure (defaultName, restored)
                           PatMatch => pure (Nothing, Nothing)
                    -- Use a unique recovered name, or an anonymous '_' when no such name is available.
                    pure (\fc => maybe (Implicit fc True) (IBindVar fc) defaultName, restored)
                  -- Keep the implicit-hole '?' representation
                  _ => pure (\fc => Implicit fc False, Nothing)
           case restored of
                Just caseTm =>
                  -- Original clauses preserve source names and nested patterns.
                  pure (caseTm, gErased fc)
                Nothing => do
                  -- Without original clauses, display the core case tree.
                  (sc', _) <- unelabTy' umode nest env sc
                  (scty', _) <- unelabTy' umode nest env scty
                  alts' <- traverse (unelabAlt defaultPat) alts
                  pure (ICase fc [] sc' scty' alts', gErased fc)
    where
      defaultPatternName : Name -> Core (Maybe Name)
      defaultPatternName n
          = do Just (argpos, pats) <- caseBlockPats n
                    | Nothing => pure Nothing
               pure $ case nub (mapMaybe (clauseDefaultName argpos) pats) of
                           [name] => Just name
                           _ => Nothing
        where
          patternVar : {vars : _} -> Term vars -> Maybe Name
          patternVar (As _ _ _ pat) = patternVar pat
          patternVar (Local _ _ _ p) = Just (nameAt p)
          patternVar _ = Nothing

          clauseDefaultName : Nat -> Clause -> Maybe Name
          clauseDefaultName argpos (MkClause _ lhs _)
              = case map fst (indexElem argpos (snd (getFnArgsSpine lhs))) of
                     Just (_, pat) => patternVar pat
                     _ => Nothing

      unelabScope : {vars : _} ->
                    FC -> Name -> SnocList (Maybe Name, Name) ->
                    Env Term vars -> NF [<] ->
                    CaseScope vars -> Core IImpClause
      unelabScope fc n args env _ (RHS fs tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               forced <- traverse (\ (MkVar v, t) =>
                       do (t', _) <- unelabTy' umode nest env t
                          pure (nameAt v, t')) fs
               let n' = MkKindedName (Just Bound) n n
               pure (PatClause fc (applySpine forced (IVar fc n') args) tm')
        where
          patVar : List (Name, IRawImp) -> Name -> IRawImp
          patVar forced arg
              = case lookup arg forced of
                     Just t =>
                       IAs fc EmptyFC UseLeft arg
                           (IMustUnify fc UserDotted t)
                     Nothing =>
                       IBindVar fc arg

          applySpine : List (Name, IRawImp) ->
                       IRawImp -> SnocList (Maybe Name, Name) -> IRawImp
          applySpine forced fn [<] = fn
          applySpine forced fn (args :< (Nothing, arg))
              = IApp fc (applySpine forced fn args)
                        (patVar forced arg)
          applySpine forced fn (args :< (Just n, arg))
              = case umode of
                     ImplicitHoles => applySpine forced fn args
                     _ => INamedApp fc (applySpine forced fn args) n
                                       (patVar forced arg)

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

      unelabAlt : (FC -> IRawImp) -> CaseAlt vars -> Core IImpClause
      unelabAlt _ (ConCase fc n t sc)
          = do defs <- get Ctxt
               nty <- lookupTyExact n (gamma defs)
               let ty = case nty of
                             Nothing => Erased fc Placeholder
                             Just t => t
               unelabScope fc !(getFullName n) [<] env !(expand !(nf [<] ty)) sc
      unelabAlt _ (DelayCase fc t a tm)
          = do let env' = env :<
                       PVar fc top Explicit (Erased fc Placeholder) :<
                       PVar fc erased Implicit (Erased fc Placeholder)
               (tm', _) <- unelabTy' umode nest env' tm
               pure (PatClause fc (IDelay fc (IBindVar fc a)) tm')
      unelabAlt _ (ConstCase fc c tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               pure (PatClause fc (IPrimVal fc c) tm')
      unelabAlt defaultPat (DefaultCase fc tm)
          = do (tm', _) <- unelabTy' umode nest env tm
               pure (PatClause fc (defaultPat fc) tm')

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
