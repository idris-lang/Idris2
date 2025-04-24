module Core.Evaluate.Quote

-- Quoting evaluated values back to Terms

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate.Value

import Data.Vect
import Libraries.Data.WithDefault

data QVar : Type where

genName : Ref QVar Int => String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

data Strategy
  = NF (Maybe (List Namespace)) -- full normal form. If a namespace list is
                                -- given, these are the ones where we can
                                -- reduce 'export' names
  | HNF (Maybe (List Namespace)) -- head normal form (block under constructors)
  | Binders -- block after going under all the binders
  | OnePi (List Namespace) -- block after getting the top level Pi binder
  | BlockApp -- block all applications
  | ExpandHoles -- block all applications except holes

Show Strategy where
  show (NF _) = "NF"
  show (HNF _) = "HNF"
  show Binders = "Binders"
  show BlockApp = "BlockApp"
  show (OnePi _) = "OnePi"
  show ExpandHoles = "Holes"

getNS : Strategy -> Maybe (List Namespace)
getNS (NF ns) = ns
getNS (HNF ns) = ns
getNS (OnePi ns) = Just ns
getNS _ = Nothing

{-
On Strategy: when quoting to full NF, we still want to block the body of an
application if it turns out to be a case expression or primitive. This is
primarily for readability of the result because we want to see the function
that was blocked, not its complete definition.
-}

applySpine : Term vars -> SnocList (FC, RigCount, Term vars) -> Term vars
applySpine tm [<] = tm
applySpine tm (args :< (fc, q, arg)) = App fc (applySpine tm args) q arg

parameters {auto c : Ref Ctxt Defs} {auto q : Ref QVar Int}

  quoteGen : {bound, vars : _} ->
             Bounds bound -> Env Term vars ->
             Value f vars -> Strategy -> Core (Term (vars ++ bound))

  -- probably ought to make traverse work on SnocList/Vect too
  quoteSpine : {bound, vars : _} ->
               Strategy -> Bounds bound -> Env Term vars ->
               Spine vars -> Core (SnocList (FC, RigCount, Term (vars ++ bound)))
  quoteSpine s bounds env [<] = pure [<]
  quoteSpine s bounds env (args :< MkSpineEntry fc q arg)
      = pure $ !(quoteSpine s bounds env args) :<
               (fc, q, !(quoteGen bounds env !arg s))

  mkTmp : FC -> Name -> Glued vars
  mkTmp fc n = vRef fc Bound n

  mkTmpVar : FC -> Name -> Core (Glued vars)
  mkTmpVar fc n = pure $ mkTmp fc n

  quoteAlt : {bound, vars : _} ->
             Strategy -> Bounds bound -> Env Term vars ->
             VCaseAlt vars -> Core (CaseAlt (vars ++ bound))
  quoteAlt {vars} s bounds env (VConCase fc n t a sc)
      = do sc' <- quoteScope a bounds sc
           pure $ ConCase fc n t sc'
    where
      -- If forced equality is still var = tm after evaluation, then keep it,
      -- otherwise it's been substituted so no longer useful
      toForced : forall vars . (Term vars, Term vars) -> Maybe (Var vars, Term vars)
      toForced (Local _ _ _ p, tm) = Just (MkVar p, tm)
      toForced _ = Nothing

      quoteScope : {bound : _} ->
                   (args : SnocList (RigCount, Name)) ->
                   Bounds bound ->
                   VCaseScope args vars ->
                   Core (CaseScope (vars ++ bound))
      quoteScope {bound} [<] bounds rhs_in
          = do (fs, rhs) <- rhs_in
               rhs' <- quoteGen bounds env rhs s
               qfs <- traverse
                           (\ (n, v) => pure (!(quoteGen bounds env n s),
                                              !(quoteGen bounds env v s)))
                           fs
               pure (RHS (mapMaybe toForced qfs) rhs')
      quoteScope (as :< (r, a)) bounds sc
          = do an <- genName "c"
               let sc' = sc (mkTmpVar fc an)
               rhs' <- quoteScope as (Add a an bounds) sc'
               pure (Arg r a rhs')

  quoteAlt s bounds env (VDelayCase fc ty arg sc)
      = do tyn <- genName "ty"
           argn <- genName "arg"
           (fs, rhs) <- sc (mkTmpVar fc tyn) (mkTmpVar fc argn)
           sc' <- quoteGen (Add arg argn (Add ty tyn bounds)) env
                           rhs s
           pure (DelayCase fc ty arg sc')
  quoteAlt s bounds env (VConstCase fc c sc)
      = do sc' <- quoteGen bounds env sc s
           pure (ConstCase fc c sc')
  quoteAlt s bounds env (VDefaultCase fc sc)
      = do sc' <- quoteGen bounds env sc s
           pure (DefaultCase fc sc')

  quotePi : {bound, vars : _} ->
            Strategy -> Bounds bound -> Env Term vars ->
            PiInfo (Glued vars) -> Core (PiInfo (Term (vars ++ bound)))
  quotePi s bounds env Explicit = pure Explicit
  quotePi s bounds env Implicit = pure Implicit
  quotePi s bounds env AutoImplicit = pure AutoImplicit
  quotePi s bounds env (DefImplicit t)
      = do t' <- quoteGen bounds env t s
           pure (DefImplicit t')

  quoteBinder : {bound, vars : _} ->
                Strategy -> Bounds bound -> Env Term vars ->
                Binder (Glued vars) -> Core (Binder (Term (vars ++ bound)))
  quoteBinder s bounds env (Lam fc r p ty)
      = do ty' <- quoteGen bounds env ty s
           p' <- quotePi s bounds env p
           pure (Lam fc r p' ty')
  quoteBinder s bounds env (Let fc r val ty)
      = do ty' <- quoteGen bounds env ty s
           val' <- quoteGen bounds env val s
           pure (Let fc r val' ty')
  quoteBinder s bounds env (Pi fc r p ty)
      = do ty' <- quoteGen bounds env ty s
           p' <- quotePi s bounds env p
           pure (Pi fc r p' ty')
  quoteBinder s bounds env (PVar fc r p ty)
      = do ty' <- quoteGen bounds env ty s
           p' <- quotePi s bounds env p
           pure (PVar fc r p' ty')
  quoteBinder s bounds env (PLet fc r val ty)
      = do ty' <- quoteGen bounds env ty s
           val' <- quoteGen bounds env val s
           pure (PLet fc r val' ty')
  quoteBinder s bounds env (PVTy fc r ty)
      = do ty' <- quoteGen bounds env ty s
           pure (PVTy fc r ty')

--   Declared above as:
--   quoteGen : {bound, vars : _} ->
--              Strategy -> Bounds bound -> Env Term vars ->
--              Value f vars -> Core (Term (vars ++ bound))
  quoteGen bounds env (VBind fc x b sc) s
      = do var <- genName "qv"
           let s' = case s of
                         Binders => BlockApp
                         _ => s
           b' <- quoteBinder s' bounds env b
           let s' = case s of
                         OnePi _ => BlockApp
                         _ => s
           sc' <- quoteGen (Add x var bounds) env
                             !(sc (mkTmpVar fc var)) s'
           pure (Bind fc x b' sc')
  -- These are the names we invented when quoting the scope of a binder
  quoteGen bounds env (VApp fc Bound (MN n i) sp val) s
      = do sp' <- quoteSpine BlockApp bounds env sp
           case findName bounds of
                Just (MkVar p) =>
                    pure $ applySpine (Local fc Nothing _ (varExtend p)) sp'
                Nothing =>
                    pure $ applySpine (Ref fc Bound (MN n i)) sp'
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
  quoteGen bounds env (VApp fc nt n sp val) BlockApp
      = do sp' <- quoteSpine BlockApp bounds env sp
           pure $ applySpine (Ref fc nt n) sp'
  quoteGen bounds env (VApp fc nt n sp val) ExpandHoles
      = do sp' <- quoteSpine ExpandHoles bounds env sp
           pure $ applySpine (Ref fc nt n) sp'
  quoteGen bounds env v@(VApp fc nt n sp val) s
      = do -- Reduce if it's visible in the current namespace
           logC "eval.ref" 50 $ do pure "quoteGen VApp \{show !(toFullNames v)}"
           True <- case getNS s of
                        Nothing => pure True
                        Just ns => do full_name <- toFullNames n
                                      vis <- getVisibility fc n
                                      -- TODO: Query context once
                                      logC "eval.ref" 50 $ do pure "quoteGen VApp with NS: \{show n} (\{show full_name}) \{show $ collapseDefault vis} in \{show ns}"
                                      pure $ reducibleInAny ns full_name $ collapseDefault vis
              | False =>
                  do sp' <- quoteSpine s bounds env sp
                     pure $ applySpine (Ref fc nt n) sp'
           Just v <- val
              | Nothing =>
                  do sp' <- quoteSpine s bounds env sp
                     pure $ applySpine (Ref fc nt n) sp'
           case s of
             -- If the result is a binder, and we're in Binder mode, then
             -- keep going, otherwise just give back the application
                Binders =>
                    if !(isBinder v)
                       then quoteGen bounds env v s
                       else do sp' <- quoteSpine s bounds env sp
                               pure $ applySpine (Ref fc nt n) sp'
             -- If the result is blocked by a case/lambda then just give back
             -- the application for readability. Otherwise, keep quoting
                _ => if !(blockedApp v)
                        then do sp' <- quoteSpine s bounds env sp
                                pure $ applySpine (Ref fc nt n) sp'
                        else quoteGen bounds env v s
    where
      isBinder : forall f . Value f vars -> Core Bool
      isBinder (VBind{}) = pure True
      isBinder _ = pure False

      blockedApp : forall f . Value f vars -> Core Bool
      blockedApp (VBind fc _ (Lam {}) sc)
          = blockedApp !(sc $ pure $ VErased fc Placeholder)
      blockedApp (VCase _ PatMatch _ _ _ _) = pure True
      blockedApp (VPrimOp{}) = pure True
      blockedApp _ = pure False
  quoteGen {bound} bounds env (VLocal fc idx p sp) s
      = do sp' <- quoteSpine s bounds env sp
           let MkVar p' = addLater bound p
           pure $ applySpine (Local fc Nothing _ p') sp'
    where
      addLater : {idx : _} ->
                 (ys : SnocList Name) -> (0 p : IsVar n idx xs) ->
                 Var (xs ++ ys)
      addLater [<] isv = MkVar isv
      addLater (xs :< x) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteGen bounds env (VMeta fc n i args sp val) BlockApp
      = do sp' <- quoteSpine BlockApp bounds env sp
           args' <- traverse (\ (q, val) =>
                                do val' <- quoteGen bounds env !val BlockApp
                                   pure (q, val')) args
           pure $ applySpine (Meta fc n i args') sp'
  quoteGen bounds env (VMeta fc n i args sp val) s
      = do Just v <- val
              | Nothing =>
                  do sp' <- quoteSpine s bounds env sp
                     args' <- traverse (\ (q, val) =>
                                          do val' <- quoteGen bounds env !val s
                                             pure (q, val')) args
                     pure $ applySpine (Meta fc n i args') sp'
           quoteGen bounds env v s
  quoteGen bounds env (VDCon fc n t a sp) s
      = do let s' = case s of
                         HNF _ => BlockApp
                         _ => s
           sp' <- quoteSpine s' bounds env sp
           pure $ applySpine (Ref fc (DataCon t a) n) sp'
  quoteGen bounds env (VTCon fc n a sp) s
      = do let s' = case s of
                         HNF _ => BlockApp
                         _ => s
           sp' <- quoteSpine s' bounds env sp
           pure $ applySpine (Ref fc (TyCon a) n) sp'
  quoteGen bounds env (VAs fc use as pat) s
      = do pat' <- quoteGen bounds env pat s
           as' <- quoteGen bounds env as s
           pure (As fc use as' pat')
  quoteGen bounds env (VCase fc t rig sc scTy alts) s
      = do sc' <- quoteGen bounds env sc s
           scTy' <- quoteGen bounds env scTy s
           let s' = case s of
                         NF _ => ExpandHoles
                         ExpandHoles => ExpandHoles
                         _ => BlockApp
           alts' <- traverse (quoteAlt s' bounds env) alts
           pure $ Case fc t rig sc' scTy' alts'
  quoteGen bounds env (VDelayed fc r ty) s
      = do ty' <- quoteGen bounds env ty s
           pure (TDelayed fc r ty')
  quoteGen bounds env (VDelay fc r ty arg) s
      = do ty' <- quoteGen bounds env ty BlockApp
           arg' <- quoteGen bounds env arg BlockApp
           pure (TDelay fc r ty' arg')
  quoteGen bounds env (VForce fc r val sp) s
      = do sp' <- quoteSpine s bounds env sp
           val' <- quoteGen bounds env val s
           pure $ applySpine (TForce fc r val') sp'
  quoteGen bounds env (VPrimVal fc c) s = pure $ PrimVal fc c
  quoteGen {vars} {bound} bounds env (VPrimOp fc fn args) s
      = do args' <- quoteArgs args
           pure $ PrimOp fc fn args'
    where
      -- No traverse for Vect in Core...
      quoteArgs : forall f . Vect n (Value f vars) -> Core (Vect n (Term (vars ++ bound)))
      quoteArgs [] = pure []
      quoteArgs (a :: as)
          = pure $ !(quoteGen bounds env a s) :: !(quoteArgs as)
  quoteGen bounds env (VErased fc why) s
     = Erased fc <$> traverse @{%search} @{CORE} (\t => quoteGen bounds env t s) why
  quoteGen bounds env (VUnmatched fc str) s = pure $ Unmatched fc str
  quoteGen bounds env (VType fc n) s = pure $ TType fc n

parameters {auto c : Ref Ctxt Defs}
  quoteStrategy : { vars : _ } -> Strategy -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteStrategy s env val
      = do q <- newRef QVar 100
           logC "eval.ref" 50 $ do
                val <- logQuiet $ quoteGen None env val BlockApp -- same as logNF
                val <- toFullNames val
                pure "Begin quote \{show s} for \{show val}"
           logDepth $ quoteGen None env val s

  export
  quoteNFall : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteNFall = quoteStrategy (NF Nothing)

  export
  quoteHNFall : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteHNFall = quoteStrategy (HNF Nothing)

  export
  quoteNF : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteNF env val
      = do defs <- get Ctxt
           quoteStrategy (NF (Just (currentNS defs :: nestedNS defs)))
                         env val

  export
  quoteHNF : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteHNF env val
      = do defs <- get Ctxt
           quoteStrategy (HNF (Just (currentNS defs :: nestedNS defs)))
                         env val

  -- Keep quoting while we're still going under binders
  export
  quoteBinders : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteBinders = quoteStrategy Binders

  -- Keep quoting while we're still going under binders
  export
  quoteOnePi : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteOnePi env val
      = do defs <- get Ctxt
           quoteStrategy (OnePi (currentNS defs :: nestedNS defs)) env val

  export
  quoteHoles : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quoteHoles = quoteStrategy ExpandHoles

  export
  quote : { vars : _ } -> Env Term vars -> Value f vars -> Core (Term vars)
  quote = quoteStrategy BlockApp
