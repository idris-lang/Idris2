module TTImp.Elab.App

import Core.Env
import Core.Metadata
import Core.Unify
import Core.Evaluate.Value
import Core.Evaluate.Quote
import Core.Evaluate.Normalise
import Core.Evaluate.Convert
import Core.Evaluate.Expand
import Core.Evaluate

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Dot
import TTImp.TTImp

import Data.SnocList
import Data.Maybe

import Libraries.Data.List.Extra
import Libraries.Data.NatSet
import Libraries.Data.VarSet
import Libraries.Data.WithDefault

%default covering

checkVisibleNS : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Visibility -> Core ()
checkVisibleNS fc (NS ns x) vis
    = if !(isVisible ns)
         then if !isAllPublic
                       || visibleInAny (!getNS :: !getNestedNS) (NS ns x) vis
                 then pure ()
                 else throw $ InvisibleName fc (NS ns x) Nothing
         else throw $ InvisibleName fc (NS ns x) (Just ns)
checkVisibleNS _ _ _ = pure ()

onLHS : ElabMode -> Bool
onLHS (InLHS _) = True
onLHS _ = False

-- Get the type of a variable, assuming we haven't found it in the nested
-- names. Look in the Env first, then the global context.
getNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto e : Ref EST (EState vars)} ->
              ElabMode ->
              RigCount -> Env Term vars ->
              FC -> Name ->
              Core (Term vars, Glued vars)
getNameType elabMode rigc env fc x
    = case defined x env of
           Just (MkIsDefined rigb lv) =>
              do rigSafe rigb rigc
                 let binder = getBinder lv env
                 let bty = binderType binder

                 log "metadata.names" 7 $ "getNameType is adding ↓"
                 addNameType fc x env bty

                 when (isLinear rigb) $ update EST { linearUsed $= VarSet.insert (MkVar lv) }
                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add Bound: "
                      ++ show x ++ " (" ++ show fc ++ ")"
                 when (isSourceName x) $
                   whenJust (isConcreteFC fc) $ \nfc => do
                     log "ide-mode.highlight" 7 $ "getNameType is adding Bound: " ++ show x
                     addSemanticDecorations [(nfc, Bound, Just x)]

                 pure (Local fc (Just (isLet binder)) _ lv, !(nf env bty))
           Nothing =>
              do defs <- get Ctxt
                 [(pname, i, def)] <- lookupCtxtName x (gamma defs)
                      | ns => ambiguousName fc x (map fst ns)
                 checkVisibleNS fc (fullname def) (collapseDefault $ visibility def)
                 when (not $ onLHS elabMode) $
                   checkDeprecation fc def
                 rigSafe (multiplicity def) rigc
                 let nt = getDefNameType def

                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add something for: "
                      ++ show def.fullname ++ " (" ++ show fc ++ ")"
                 logEnv "ide-mode.highlight" 8 "getNameType Nothing Env" env
                 logTerm "ide-mode.highlight" 8 "getNameType Nothing type def of \{show x}" (type def)

                 when (isSourceName def.fullname) $
                   whenJust (isConcreteFC fc) $ \nfc => do
                     let decor = ifThenElse (isEscapeHatch def) Postulate (nameDecoration def.fullname nt)
                     log "ide-mode.highlight" 7
                       $ "getNameType is adding " ++ show decor ++ ": " ++ show def.fullname
                     addSemanticDecorations [(nfc, decor, Just def.fullname)]

                 logTerm "ide-mode.highlight" 8 "def" (embed {outer=vars} (type def))
                 pure (Ref fc nt (Resolved i), !(nf env (embed (type def))))
  where
    rigSafe : RigCount -> RigCount -> Core ()
    rigSafe lhs rhs = when (lhs < rhs)
                           (throw (LinearMisuse fc !(getFullName x) lhs rhs))

    checkDeprecation : FC -> GlobalDef -> Core ()
    checkDeprecation fc gdef =
      do when (Deprecate `elem` gdef.flags) $
           recordWarning $
             Deprecated fc
               "\{show gdef.fullname} is deprecated and will be removed in a future version."
               (Just (fc, gdef.fullname))

-- Get the type of a variable, looking it up in the nested names first.
getVarType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto e : Ref EST (EState vars)} ->
             ElabMode ->
             RigCount -> NestedNames vars -> Env Term vars ->
             FC -> Name ->
             Core (Term vars, Nat, Glued vars)
getVarType elabMode rigc nest env fc x
    = case lookup x (names nest) of
           Nothing => do (tm, ty) <- getNameType elabMode rigc env fc x
                         pure (tm, 0, ty)
           Just (nestn, argns, tmf) =>
              do defs <- get Ctxt
                 let arglen = length argns
                 let n' = fromMaybe x nestn
                 case !(lookupCtxtExact n' (gamma defs)) of
                      Nothing => undefinedName fc n'
                      Just ndef =>
                         let nt = getDefNameType ndef
                             tm = tmf fc nt
                             tyenv = useVars (getArgs tm)
                                             (embed (type ndef)) in
                             do checkVisibleNS fc (fullname ndef) (collapseDefault $ visibility ndef)
                                logTerm "elab" 5 ("Type of " ++ show n') tyenv
                                logTerm "elab" 5 ("Expands to") tm
                                log "elab" 5 $ "Arg length " ++ show arglen

                                -- Add the type to the metadata
                                log "metadata.names" 7 $ "getVarType is adding ↓"
                                addNameType fc x env tyenv

                                when (isSourceName ndef.fullname) $
                                  whenJust (isConcreteFC fc) $ \nfc => do
                                    let decor = nameDecoration ndef.fullname nt
                                    log "ide-mode.highlight" 7
                                       $ "getNameType is adding "++ show decor ++": "
                                                                 ++ show ndef.fullname
                                    addSemanticDecorations [(nfc, decor, Just ndef.fullname)]

                                pure (tm, arglen, !(nf env tyenv))
    where
      useVars : {vars : _} ->
                List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind bfc n (Pi fc c _ ty) sc)
           = Bind bfc n (Let fc c a ty) (useVars (map weaken as) sc)
      useVars as (Bind bfc n (Let fc c v ty) sc)
           = Bind bfc n (Let fc c v ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

isHole : NF vars -> Bool
isHole (VMeta{}) = True
isHole _ = False

mutual
  makeImplicit : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> RigCount ->
                 Name -> Glued vars -> (Core (Glued vars) -> Core (Glued vars)) ->
                 (argdata : (Maybe Name, Nat)) ->
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  makeImplicit rig argRig elabinfo nest env fc tm tmrig x aty sc (n, argpos) expargs autoargs namedargs kr expty
      = do defs <- get Ctxt
           nm <- genMVName x
           empty <- clearDefs defs
           metaty <- quote env aty
           metaval <- metaVar fc argRig env nm metaty
           let fntm = App fc tm tmrig metaval
           fnty <- expand !(sc (nf env metaval))
           when (bindingVars elabinfo) $ update EST $
             addBindIfUnsolved nm (getLoc (getFn tm)) argRig Implicit env metaval metaty
           checkAppWith rig elabinfo nest env fc
                        fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

  makeAutoImplicit : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     {auto e : Ref EST (EState vars)} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     RigCount -> RigCount -> ElabInfo ->
                     NestedNames vars -> Env Term vars ->
                     FC -> (fntm : Term vars) -> RigCount ->
                     Name -> Glued vars -> (Core (Glued vars) -> Core (Glued vars)) ->
                     (argpos : (Maybe Name, Nat)) ->
                     (expargs : List RawImp) ->
                     (autoargs : List RawImp) ->
                     (namedargs : List (Name, RawImp)) ->
                     (knownret : Bool) ->
                     (expected : Maybe (Glued vars)) ->
                     Core (Term vars, Glued vars)
  makeAutoImplicit rig argRig elabinfo nest env fc tm tmrig x aty sc (n, argpos) expargs autoargs namedargs kr expty
  -- on the LHS, just treat it as an implicit pattern variable.
  -- on the RHS, add a searchable hole
      = if metavarImp (elabMode elabinfo)
           then do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote env aty
                   metaval <- metaVar fc argRig env nm metaty
                   let fntm = App fc tm tmrig metaval
                   fnty <- expand !(sc (nf env metaval))
                   update EST $ addBindIfUnsolved nm (getLoc (getFn tm)) argRig AutoImplicit env metaval metaty
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           else do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote env aty
                   est <- get EST
                   lim <- getAutoImplicitLimit
                   metaval <- searchVar fc argRig lim (Resolved (defining est))
                                        env nest nm metaty
                   let fntm = App fc tm tmrig metaval
                   fnty <- expand !(sc (nf env metaval))
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
    where
      metavarImp : ElabMode -> Bool
      metavarImp (InLHS _) = True
      metavarImp InTransform = True
      metavarImp _ = False

  makeDefImplicit : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto m : Ref MD Metadata} ->
                    {auto u : Ref UST UState} ->
                    {auto e : Ref EST (EState vars)} ->
                    {auto s : Ref Syn SyntaxInfo} ->
                    {auto o : Ref ROpts REPLOpts} ->
                    RigCount -> RigCount -> ElabInfo ->
                    NestedNames vars -> Env Term vars ->
                    FC -> (fntm : Term vars) -> RigCount ->
                    Name -> Glued vars -> Glued vars ->
                    (Core (Glued vars) -> Core (Glued vars)) ->
                    (argpos : (Maybe Name, Nat)) ->
                    (expargs : List RawImp) ->
                    (autoargs : List RawImp) ->
                    (namedargs : List (Name, RawImp)) ->
                    (knownret : Bool) ->
                    (expected : Maybe (Glued vars)) ->
                    Core (Term vars, Glued vars)
  makeDefImplicit rig argRig elabinfo nest env fc tm tmrig x arg aty sc (n, argpos) expargs autoargs namedargs kr expty
  -- on the LHS, just treat it as an implicit pattern variable.
  -- on the RHS, use the default
      = if metavarImp (elabMode elabinfo)
           then do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote env aty
                   metaval <- metaVar fc argRig env nm metaty
                   let fntm = App fc tm tmrig metaval
                   fnty <- expand !(sc (nf env metaval))
                   update EST $ addBindIfUnsolved nm (getLoc (getFn tm)) argRig AutoImplicit env metaval metaty
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           else do defs <- get Ctxt
                   empty <- clearDefs defs
                   aval <- quote env arg
                   let fntm = App fc tm tmrig aval
                   fnty <- expand !(sc (pure arg))
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
    where
      metavarImp : ElabMode -> Bool
      metavarImp (InLHS _) = True
      metavarImp InTransform = True
      metavarImp _ = False

  -- Defer elaborating anything which will be easier given a known target
  -- type (ambiguity, cases, etc)
  needsDelayExpr : {auto c : Ref Ctxt Defs} ->
                   (knownRet : Bool) -> RawImp ->
                   Core Bool
  needsDelayExpr False _ = pure False
  needsDelayExpr True (IVar fc n)
      = do defs <- get Ctxt
           pure $ case !(lookupCtxtName n (gamma defs)) of
                       (_ :: _ :: _) => True
                       _ => False
  needsDelayExpr True (IApp _ f _) = needsDelayExpr True f
  needsDelayExpr True (IAutoApp _ f _) = needsDelayExpr True f
  needsDelayExpr True (INamedApp _ f _ _) = needsDelayExpr True f
  needsDelayExpr True (ILam {}) = pure True
  needsDelayExpr True (ICase {}) = pure True
  needsDelayExpr True (ILocal {}) = pure True
  needsDelayExpr True (IUpdate {}) = pure True
  needsDelayExpr True (IAlternative {}) = pure True
  needsDelayExpr True (ISearch {}) = pure True
  needsDelayExpr True (IRewrite {}) = pure True
  needsDelayExpr True _ = pure False

  -- On the LHS, for any concrete thing, we need to make sure we know
  -- its type before we proceed so that we can reject it if the type turns
  -- out to be polymorphic
  needsDelayLHS : {auto c : Ref Ctxt Defs} ->
                  RawImp -> Core Bool
  needsDelayLHS (IVar fc n) = pure True
  needsDelayLHS (IApp _ f _) = needsDelayLHS f
  needsDelayLHS (IAutoApp _ f _) = needsDelayLHS f
  needsDelayLHS (INamedApp _ f _ _) = needsDelayLHS f
  needsDelayLHS (IAlternative {}) = pure True
  needsDelayLHS (IAs _ _ _ _ t) = needsDelayLHS t
  needsDelayLHS (ISearch {}) = pure True
  needsDelayLHS (IPrimVal {}) = pure True
  needsDelayLHS (IType _) = pure True
  needsDelayLHS (IWithUnambigNames _ _ t) = needsDelayLHS t
  needsDelayLHS _ = pure False

  needsDelay : {auto c : Ref Ctxt Defs} ->
               ElabMode ->
               (knownRet : Bool) -> RawImp ->
               Core Bool
  needsDelay (InLHS _) _ tm = needsDelayLHS tm
  needsDelay _ kr tm = needsDelayExpr kr tm

  checkValidPattern :
    {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    {auto e : Ref EST (EState vars)} ->
    RigCount -> Env Term vars -> FC ->
    Term vars -> Glued vars ->
    Core (Term vars, Glued vars)
  checkValidPattern rig env fc tm ty
    = do log "elab.app.lhs" 50 $ "Checking that " ++ show tm ++ " is a valid pattern"
         case tm of
           Bind _ _ (Lam {}) _ => registerDot rig env fc NotConstructor tm ty
           _ => pure (tm, ty)

  dotErased : {vars : _} ->
              {auto c : Ref Ctxt Defs} -> (argty : Glued vars) ->
              Maybe Name -> Nat -> ElabMode -> RigCount -> RawImp -> Core RawImp
  dotErased argty mn argpos (InLHS lrig ) rig tm
      = if not (isErased lrig) && isErased rig
          then do
            -- if the argument type aty has a single constructor, there's no need
            -- to dot it
            defs <- get Ctxt
            nfargty <- expand argty
            mconsCount <- countConstructors nfargty
            logNF "elab.app.dot" 50
              "Found \{show mconsCount} constructors for type"
              (mkEnv emptyFC vars)
              nfargty
            if mconsCount == Just 1 || mconsCount == Just 0
              then pure tm
              else
                -- if argpos is an erased position of 'n', leave it, otherwise dot if
                -- necessary
                do Just gdef <- maybe (pure Nothing) (\n => lookupCtxtExact n (gamma defs)) mn
                        | Nothing => pure (dotTerm tm)
                   if argpos `elem` safeErase gdef
                      then pure tm
                      else pure $ dotTerm tm
          else pure tm
    where
      -- TODO: this seems too conservative. If we get back an expression stuck on a
      -- meta, shouldn't we delay the check instead of declaring the tm dotted?
      ||| Count the constructors of a fully applied concrete datatype
      countConstructors : NF vars -> Core (Maybe Nat)
      countConstructors (VTCon _ tycName n args) =
        if length args == n
        then do defs <- get Ctxt
                Just gdef <- lookupCtxtExact tycName (gamma defs)
                | Nothing => pure Nothing
                let (TCon _ _ _ _ _ datacons _) = gdef.definition
                | _ => pure Nothing
                pure (length <$> datacons)
        else pure Nothing
      countConstructors _ = pure Nothing

      dotTerm : RawImp -> RawImp
      dotTerm tm
          = case tm of
                 IMustUnify {} => tm
                 IBindVar {} => tm
                 Implicit {} => tm
                 IAs _ _ _ _ (IBindVar {}) => tm
                 IAs _ _ _ _ (Implicit {}) => tm
                 IAs fc nameFC p t arg => IAs fc nameFC p t (IMustUnify fc ErasedArg tm)
                 _ => IMustUnify (getFC tm) ErasedArg tm
  dotErased _ _ _ _ _ tm = pure tm

  -- Check the rest of an application given the argument type and the
  -- raw argument. We choose elaboration order depending on whether we know
  -- the return type now. If we know it, elaborate the rest of the
  -- application first and come back to it, because that might infer types
  -- for implicit arguments, which might in turn help with type-directed
  -- disambiguation when elaborating the argument.
  checkRestApp : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> Name ->
                 RigCount -> (aty : Glued vars) -> (sc : Core (Glued vars) -> Core (Glued vars)) ->
                 (argdata : (Maybe Name, Nat)) ->
                 (arg : RawImp) ->
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  checkRestApp rig argRig elabinfo nest env fc tm x rigb aty sc
               (n, argpos) arg_in expargs autoargs namedargs knownret expty
     = do log "elab" 10 ("arg_in: " ++ show arg_in)
          arg <- dotErased aty n argpos (elabMode elabinfo) argRig arg_in
          log "elab" 10 ("arg: " ++ show arg)
          kr <- if knownret
                   then pure True
                   else do sc' <- sc (pure (VErased fc Placeholder))
                           concrete env !(expand sc')
          -- In theory we can check the arguments in any order. But it turns
          -- out that it's sometimes better to do the rightmost arguments
          -- first to give ambiguity resolution more to work with. So
          -- we do that if the target type is unknown, or if we see that
          -- the raw term is otherwise worth delaying.
          if (isHole !(expand aty) && kr) || !(needsDelay (elabMode elabinfo) kr arg_in)
             then handle (checkRtoL kr arg)
                  -- if the type isn't resolved, we might encounter an
                  -- implicit that we can't use yet because we don't know
                  -- about it. In that case, revert to LtoR
                    (\err => if invalidArg err
                                then checkLtoR kr arg
                                else throw err)
             else checkLtoR kr arg
    where
      invalidArg : Error -> Bool
      invalidArg (InvalidArgs {}) = True
      invalidArg _ = False

      checkRtoL : Bool -> -- return type is known
                  RawImp -> -- argument currently being checked
                  Core (Term vars, Glued vars)
      checkRtoL kr arg
        = do nm <- genMVName x
             metaty <- quote env aty
             logTerm "elab" 10 "metaty: " metaty
             (idx, metaval) <- argVar (getFC arg) argRig env nm metaty
             let fntm = App fc tm rigb metaval
             logTerm "elab" 10 "...as" metaval
             fnty <- expand !(sc (nf env metaval))
             (tm, gty) <- checkAppWith rig elabinfo nest env fc
                                       fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
             logEnv "elab" 10 "Metaty Env" env
             defs <- get Ctxt
             logMetatyCtxt defs metaty
             aty' <- nf env metaty
             logNF "elab" 10 ("Now trying " ++ show nm ++ " " ++ show arg) env aty'
             atyNF <- if onLHS (elabMode elabinfo)
                         then Just <$> expand aty'
                         else pure Nothing

             -- On the LHS, checking an argument can't resolve its own type,
             -- it must be resolved from elsewhere. Otherwise we might match
             -- on things which are too specific for their polymorphic type.
             case atyNF of
                  Just (VMeta _ _ i _ _ _) =>
                          do defs <- get Ctxt
                             Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                                  | Nothing => pure ()
                             when (isErased (multiplicity gdef)) $ addNoSolve i
                  _ => pure ()
             case atyNF of
                  Just x => logNF "elab" 50 "checkRtoL atyNF" env x
                  _      => log   "elab" 50 "checkRtoL atyNF Nothing"

             res <- logDepth $ check argRig ({ topLevel := False } elabinfo) nest env arg (Just aty')
             case atyNF of
                  Just (VMeta _ _ i _ _ _) => removeNoSolve i
                  _ => pure ()

             (argv, argt) <-
               if not (onLHS (elabMode elabinfo))
                 then pure res
                 else do let (argv, argt) = res
                         checkValidPattern rig env fc argv argt

             -- If we're on the LHS, reinstantiate it with 'argv' because it
             -- *may* have as patterns in it and we need to retain them.
             -- (As patterns are a bit of a hack but I don't yet see a
             -- better way that leads to good code...)
             logTerm "elab" 10 ("Solving " ++ show !(toFullNames !(toFullNames metaval)) ++ " with") !(toFullNames !(toFullNames argv))
             logEnv "elab" 10 "In env" env
             ok <- solveIfUndefined env metaval argv
             -- If there's a constraint, make a constant, but otherwise
             -- just return the term as expected
             tm <- if not ok
                      then do res <- convert fc elabinfo env
                                                 !(nf env metaval)
                                                 !(nf env argv)
                              let [] = constraints res
                                  | cs => do tmty <- quote env gty
                                             newConstant fc rig env tm tmty cs
                              ignore $ updateSolution env metaval argv
                              pure tm
                      else pure tm
             logTerm "elab" 10 "Solved tm ok=\{show ok}" tm
             when (onLHS $ elabMode elabinfo) $
                 -- reset hole and redo it with the unexpanded definition
                 do updateDef (Resolved idx) (const (Just (Hole 0 (holeInit False))))
                    ignore $ solveIfUndefined env metaval argv
             -- Mark for reduction when we finish elaborating
             updateDef (Resolved idx)
                  (\def => case def of
                        (Function pminfo treeCT treeRT pats) =>
                           Just (Function ({alwaysReduce := True} pminfo) treeCT treeRT pats)
                        _ => Nothing
                        )
             removeHole idx
             pure (tm, gty)
        where
          logMetatyCtxt : Defs -> Term vars -> Core ()
          logMetatyCtxt defs (Meta _ _ idx _) = do
            m_metagdef <- lookupCtxtExact (Resolved idx) (gamma defs)
            log "elab" 10 $ "Meta definition from " ++ show idx ++ ": " ++ show (map definition m_metagdef)
            pure ()
          logMetatyCtxt _ _ = pure ()

      checkLtoR : Bool -> -- return type is known
                  RawImp -> -- argument currently being checked
                  Core (Term vars, Glued vars)
      checkLtoR kr arg
        = do logNF "elab" 10 ("Full function type") env
                   (VBind {f=Normal} fc x (Pi fc argRig Explicit aty) sc)
             logC "elab" 10
                     (do ety <- maybe (pure Nothing)
                                     (\t => pure (Just !(toFullNames !(quote env t))))
                                     expty
                         pure ("Overall expected type: " ++ show ety))
             res <- logDepth $ check argRig ({ topLevel := False } elabinfo)
                                   nest env arg (Just aty)
             (argv, argt) <-
               if not (onLHS (elabMode elabinfo))
                 then pure res
                 else do let (argv, argt) = res
                         checkValidPattern rig env fc argv argt

             logNF "elab" 10 "Got arg type" env argt
             let fntm = App fc tm rigb argv
             logTerm "elab" 10 "Got fntm" fntm
             fnty <- expand !(sc (nf env argv))
             checkAppWith rig elabinfo nest env fc
                          fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

  export
  findNamed : Name -> List (Name, a) -> Maybe ((Name, a), List (Name, a))
  findNamed n = findAndDeleteBy $ (== n) . fst

  export
  findBindAllExpPattern : List (Name, RawImp) -> Maybe RawImp
  findBindAllExpPattern = lookup (UN Underscore)

  isImplicitAs : RawImp -> Bool
  isImplicitAs (IAs _ _ UseLeft _ (Implicit {})) = True
  isImplicitAs _ = False

  isBindAllExpPattern : Name -> Bool
  isBindAllExpPattern (UN Underscore) = True
  isBindAllExpPattern _ = False

  checkAppNotFnType : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  {auto e : Ref EST (EState vars)} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  RigCount -> ElabInfo ->
                  NestedNames vars -> Env Term vars ->
                  FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                  (argdata : (Maybe Name, Nat)) ->
                       -- function we're applying, and argument position, for
                       -- checking if it's okay to erase against 'safeErase'
                  (expargs : List RawImp) ->
                  (autoargs : List RawImp) ->
                  (namedargs : List (Name, RawImp)) ->
                  (knownret : Bool) -> -- Do we know what the return type is yet?
                               -- if we do, we might be able to use it to work
                               -- out the types of arguments before elaborating them
                  (expected : Maybe (Glued vars)) ->
                  Core (Term vars, Glued vars)
  -- Invent a function type if we have extra explicit arguments but type is further unknown
  checkAppNotFnType {vars} rig elabinfo nest env fc tm ty (n, argpos) (arg :: expargs) autoargs namedargs kr expty
      = -- Invent a function type,  and hope that we'll know enough to solve it
        -- later when we unify with expty
        do logNF "elab.with" 10 "Function type" env ty
           logTerm "elab.with" 10 "Function " tm
           argn <- genName "argTy"
           retn <- genName "retTy"
           u <- uniVar fc
           argTy <- metaVar fc erased env argn (TType fc u)
           argTyG <- nf env argTy
           retTy <- metaVar -- {vars = argn :: vars}
                            fc erased env -- (Pi RigW Explicit argTy :: env)
                            retn (TType fc u)
           (argv, argt) <- logDepth $ check rig elabinfo
                                 nest env arg (Just argTyG)
           let fntm = App fc tm top argv
           fnty <- nf env retTy
           expfnty <- nf env (Bind fc argn (Pi fc top Explicit argTy) (weaken retTy))
           logNF "elab.with" 10 "Expected function type" env expfnty
           -- whenJust expty (logNF "elab.with" 10 "Expected result type" env)
           res <- logDepth $ checkAppWith' rig elabinfo nest env fc fntm !(expand fnty) (n, 1 + argpos) expargs autoargs namedargs kr expty
           cres <- Check.convert fc elabinfo env (asGlued ty) expfnty
           let [] = constraints cres
              | cs => do cty <- quote env expfnty
                         ctm <- newConstant fc rig env (fst res) cty cs
                         pure (ctm, !(nf env retTy))
           pure res
  -- Only non-user implicit `as` bindings are allowed to be present as arguments at this stage
  checkAppNotFnType rig elabinfo nest env fc tm ty argdata [] autoargs namedargs kr expty
      = if all isImplicitAs (autoargs ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
           then checkExp rig elabinfo env fc tm (asGlued ty) expty
           else throw (InvalidArgs fc env (map (const (UN $ Basic "<auto>")) autoargs ++ map fst namedargs) tm)

  -- Check an application of 'fntm', with type 'fnty' to the given list
  -- of explicit and implicit arguments.
  -- Returns the checked term and its (weakly) normalised type
  checkAppWith' : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                 (argdata : (Maybe Name, Nat)) ->
                      -- function we're applying, and argument position, for
                      -- checking if it's okay to erase against 'safeErase'
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) -> -- Do we know what the return type is yet?
                              -- if we do, we might be able to use it to work
                              -- out the types of arguments before elaborating them
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
   -- Explicit Pi, we use provided unnamed explicit argument
  checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
               argdata (arg :: expargs') autoargs namedargs kr expty
     = do let argRig = rig |*| rigb
          checkRestApp rig argRig elabinfo nest env fc
                       tm x rigb aty sc argdata arg expargs' autoargs namedargs kr expty
  checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
               argdata [] autoargs namedargs kr expty with (findNamed x namedargs)
   -- We found a compatible named argument
   checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
                argdata [] autoargs namedargs kr expty | Just ((_, arg), namedargs')
    = do let argRig = rig |*| rigb
         checkRestApp rig argRig elabinfo nest env fc
                      tm x rigb aty sc argdata arg [] autoargs namedargs' kr expty
   checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
                argdata [] autoargs namedargs kr expty | Nothing
    = case findBindAllExpPattern namedargs of
           Just arg => -- Bind-all-explicit pattern is present - implicitly bind
             do let argRig = rig |*| rigb
                checkRestApp rig argRig elabinfo nest env fc
                             tm x rigb aty sc argdata arg [] autoargs namedargs kr expty
           _ =>
             do defs <- get Ctxt
                if all isImplicitAs (autoargs
                                      ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
                                                                    -- Only non-user implicit `as` bindings added by
                                                                    -- the compiler are allowed here
                   then -- We are done
                        checkExp rig elabinfo env fc tm (asGlued ty) expty
                   else -- Some user defined binding is present while we are out of explicit arguments, that's an error
                        throw (InvalidArgs fc env (map (const (UN $ Basic "<auto>")) autoargs ++ map fst namedargs) tm)
  -- Function type is delayed:
  --   RHS: force the term
  --   LHS: strip off delay but only for explicit functions and disallow any further patterns
  checkAppWith' rig elabinfo nest env fc tm dty@(VDelayed dfc r ty) argdata expargs autoargs namedargs kr expty
      = do ty' <- expand ty
           case ty' of
                VBind _ _ (Pi _ _ _ _) sc =>
                  checkAppWith' rig elabinfo nest env fc (TForce dfc r tm) !(expand ty)
                        argdata expargs autoargs namedargs kr expty
                _ => checkAppNotFnType rig elabinfo nest env fc tm dty argdata expargs autoargs namedargs kr expty
  -- If there's no more arguments given, and the plicities of the type and
  -- the expected type line up, stop
  checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Implicit aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rig |*| rigb
           expty <- expand expty_in
           defs <- get Ctxt
           case expty of
                VBind tfc' x' (Pi _ rigb' Implicit aty') sc'
                   => checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
                _ => if not (preciseInf elabinfo)
                        then makeImplicit rig argRig elabinfo nest env fc tm rigb x aty sc argdata [] [] [] kr (Just expty_in)
                        -- in 'preciseInf' mode blunder on anyway, and hope
                        -- that we can resolve the implicits
                        else handle (checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in))
                               (\err => makeImplicit rig argRig elabinfo nest env fc tm rigb x aty sc argdata [] [] [] kr (Just expty_in))
  -- Same for auto
  checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rig |*| rigb
           expty <- expand expty_in
           defs <- get Ctxt
           case expty of
                VBind tfc' x' (Pi _ rigb' AutoImplicit aty') sc'
                   => checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
                _ => makeAutoImplicit rig argRig elabinfo nest env fc tm rigb x aty sc argdata [] [] [] kr (Just expty_in)
  -- Same for default
  checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb (DefImplicit aval) aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rigMult rig rigb
           expty <- expand expty_in
           defs <- get Ctxt
           case expty of
                VBind tfc' x' (Pi _ rigb' (DefImplicit aval') aty') sc'
                   => if !(convert env aval aval')
                         then checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
                         else makeDefImplicit rig argRig elabinfo nest env fc tm rigb x aval aty sc argdata [] [] [] kr (Just expty_in)
                _ => makeDefImplicit rig argRig elabinfo nest env fc tm rigb x aval aty sc argdata [] [] [] kr (Just expty_in)

  -- Check next unnamed auto implicit argument
  checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata expargs (arg :: autoargs') namedargs kr expty
      = checkRestApp rig (rig |*| rigb) elabinfo nest env fc
                         tm x rigb aty sc argdata arg expargs autoargs' namedargs kr expty
  -- Check next named auto implicit argument
  checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata expargs [] namedargs kr expty
      = let argRig = rig |*| rigb in
            case findNamed x namedargs of
                 Just ((_, arg), namedargs') =>
                    checkRestApp rig argRig elabinfo nest env fc
                                 tm x rigb aty sc argdata arg expargs [] namedargs' kr expty
                 Nothing =>
                         makeAutoImplicit rig argRig elabinfo nest env fc tm rigb
                                              x aty sc argdata expargs [] namedargs kr expty
  -- Check next implicit argument
  checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb Implicit aty) sc)
               argdata expargs autoargs namedargs kr expty
      = let argRig = rig |*| rigb in
            case findNamed x namedargs of
               Nothing => makeImplicit rig argRig elabinfo nest env fc tm rigb
                                       x aty sc argdata expargs autoargs namedargs kr expty
               Just ((_, arg), namedargs') =>
                     checkRestApp rig argRig elabinfo nest env fc tm
                                  x rigb aty sc argdata arg expargs autoargs namedargs' kr expty
  -- Check next default argument
  checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb (DefImplicit arg) aty) sc)
               argdata expargs autoargs namedargs kr expty
      = let argRig = rigMult rig rigb in
            case findNamed x namedargs of
               Nothing => makeDefImplicit rig argRig elabinfo nest env fc tm rigb
                                          x arg aty sc argdata expargs autoargs namedargs kr expty
               Just ((_, arg), namedargs') =>
                     checkRestApp rig argRig elabinfo nest env fc
                                  tm x rigb aty sc argdata arg expargs autoargs namedargs' kr expty
  -- Invent a function type if we have extra explicit arguments but type is further unknown
  -- Invent a function type if we have extra explicit arguments but type is further unknown
  checkAppWith' rig elabinfo nest env fc tm ty argdata expargs autoargs namedargs kr expty
      = checkAppNotFnType rig elabinfo nest env fc tm ty argdata expargs autoargs namedargs kr expty

  ||| Entrypoint for checkAppWith: run the elaboration first and, if we're
  ||| on the LHS and the result is an under-applied constructor then insist
  ||| that it ought to be forced by another pattern somewhere else in the LHS.
  checkAppWith : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                 (argdata : (Maybe Name, Nat)) ->
                      -- function we're applying, and argument position, for
                      -- checking if it's okay to erase against 'safeErase'
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) -> -- Do we know what the return type is yet?
                              -- if we do, we might be able to use it to work
                              -- out the types of arguments before elaborating them
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  checkAppWith rig info nest env fc tm ty
    argdata expargs autoargs namedargs knownret expected
    = do res <- checkAppWith' rig info nest env fc tm ty
                   argdata expargs autoargs namedargs knownret expected
         let Just _ = isLHS (elabMode info)
               | Nothing => pure res
         let (Ref _ t _, args) = getFnArgs (fst res)
               | _ => pure res
         let Just a = isCon t
               | _ => pure res
         if a == length args
           then pure res
           else registerDot rig env fc UnderAppliedCon (fst res) (snd res)

export
checkApp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> (fn : RawImp) ->
           (expargs : List RawImp) ->
           (autoargs : List RawImp) ->
           (namedargs : List (Name, RawImp)) ->
           Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkApp rig elabinfo nest env fc (IApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn (arg :: expargs) autoargs namedargs exp
checkApp rig elabinfo nest env fc (IAutoApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs (arg :: autoargs) namedargs exp
checkApp rig elabinfo nest env fc (INamedApp fc' fn nm arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs autoargs ((nm, arg) :: namedargs) exp
checkApp rig elabinfo nest env fc (IVar fc' n) expargs autoargs namedargs exp
   = do logEnv "elab" 50 "checkApp-IVar Env for \{show !(getFullName n)}" env
        (ntm, arglen, nty_in) <- getVarType elabinfo.elabMode rig nest env fc' n
        logTerm "elab" 50 "checkApp-IVar ntm arglen: \{show arglen}" ntm
        logNF "elab" 50 "checkApp-IVar nty_in" env nty_in
        nty <- expand nty_in
        logNF "elab" 50 "checkApp-IVar nty" env nty

        prims <- getPrimitiveNames
        elabinfo <- updateElabInfo prims elabinfo.elabMode n expargs elabinfo

        addNameLoc fc' n

        logC "elab" 10
                (do defs <- get Ctxt
                    fnty <- logQuiet $ quote env nty
                    exptyt <- maybe (pure Nothing)
                                       (\t => do ety <- quote env t
                                                 etynf <- normaliseHoles env ety
                                                 pure (Just !(toFullNames etynf)))
                                       exp
                    pure ("Checking application of " ++ show !(getFullName n) ++
                          " (" ++ show n ++ ")" ++
                          " to " ++ show expargs ++ "\n\tFunction type " ++
                          (show !(toFullNames fnty)) ++ "\n\tExpected app type "
                                ++ show exptyt))
        let fn = mapNestedName nest n
        normalisePrims prims env
           !(checkAppWith rig elabinfo nest env fc ntm nty (Just fn, arglen) expargs autoargs namedargs False exp)
  where

    -- If the term is an application of a primitive conversion (fromInteger etc)
    -- and it's applied to a constant, fully normalise the term.
    normalisePrims : {vs : _} ->
                     List Name -> Env Term vs ->
                     (Term vs, Glued vs) ->
                     Core (Term vs, Glued vs)
    normalisePrims prims env res
        = do tm <- Evaluate.normalisePrims (`boundSafe` elabMode elabinfo)
                                            isIPrimVal
                                            (onLHS (elabMode elabinfo))
                                            prims n (cast {to=SnocList RawImp} expargs) (fst res) env
             pure (fromMaybe (fst res) tm, snd res)

      where

        boundSafe : Constant -> ElabMode -> Bool
        boundSafe _ (InLHS _) = True -- always need to expand on LHS
        -- only do this for relatively small bounds.
        -- Once it gets too big, we might be making the term
        -- bigger than it would have been without evaluating!
        boundSafe (BI x) _ = abs x < 100
        boundSafe (Str str) _ = length str < 10
        boundSafe _ _ = True

    updateElabInfo : List Name -> ElabMode -> Name ->
                     List RawImp -> ElabInfo -> Core ElabInfo
    -- If it's a primitive function applied to a constant on the LHS, treat it
    -- as an expression because we'll normalise the function away and match on
    -- the result
    updateElabInfo prims (InLHS _) n [IPrimVal fc c] elabinfo =
        do if isPrimName prims !(getFullName n)
              then pure ({ elabMode := InExpr } elabinfo)
              else pure elabinfo
    updateElabInfo _ _ _ _ info = pure info

checkApp rig elabinfo nest env fc fn expargs autoargs namedargs exp
   = do (fntm, fnty_in) <- checkImp rig elabinfo nest env fn Nothing
        fnty <- expand fnty_in
        checkAppWith rig elabinfo nest env fc fntm fnty (Nothing, 0) expargs autoargs namedargs False exp
