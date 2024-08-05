module TTImp.PartialEval

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Normalise
import Core.Value
import Core.UnifyState

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.TTImp.Traversals
import TTImp.Unelab

import Protocol.Hex

import Data.List
import Data.SnocList
import Libraries.Data.NameMap
import Libraries.Data.WithDefault

%default covering

data ArgMode' tm = Static tm | Dynamic

ArgMode : Type
ArgMode = ArgMode' ClosedTerm

traverseArgMode : (a -> Core b) -> ArgMode' a -> Core (ArgMode' b)
traverseArgMode f (Static t) = Static <$> f t
traverseArgMode f Dynamic = pure Dynamic

covering
Show a => Show (ArgMode' a) where
  show (Static tm) = "Static " ++ show tm
  show Dynamic = "Dynamic"


getStatic : ArgMode -> Maybe (Term [<])
getStatic Dynamic = Nothing
getStatic (Static t) = Just t

specialiseTy : {vars : _} ->
               Nat -> List (Nat, Term [<]) -> Term vars -> Term vars
specialiseTy i specs (Bind fc x (Pi fc' c p ty) sc)
    = case lookup i specs of
           Nothing => Bind fc x (Pi fc' c p ty) $ -- easier later if everything explicit
                        specialiseTy (1 + i) specs sc
           Just tm => specialiseTy (1 + i) specs (subst (embed tm) sc)
specialiseTy i specs tm = tm

substLoc : {vs : _} ->
           Nat -> Term vs -> Term vs -> Term vs
substLoc i tm (Local fc l idx p)
    = if i == idx then tm else (Local fc l idx p)
substLoc i tm (Bind fc x b sc)
    = Bind fc x (map (substLoc i tm) b) (substLoc (1 + i) (weaken tm) sc)
substLoc i tm (Meta fc n r args)
    = Meta fc n r (map (substLoc i tm) args)
substLoc i tm (App fc f a) = App fc (substLoc i tm f) (substLoc i tm a)
substLoc i tm (As fc s f a) = As fc s (substLoc i tm f) (substLoc i tm a)
substLoc i tm (TDelayed fc r d) = TDelayed fc r (substLoc i tm d)
substLoc i tm (TDelay fc r ty d) = TDelay fc r (substLoc i tm ty) (substLoc i tm d)
substLoc i tm (TForce fc r d) = TForce fc r (substLoc i tm d)
substLoc i tm x = x

substLocs : {vs : _} ->
            List (Nat, Term vs) -> Term vs -> Term vs
substLocs [] tm = tm
substLocs ((i, tm') :: subs) tm = substLocs subs (substLoc i tm' tm)

mkSubsts : Nat -> List (Nat, Term [<]) ->
           List (Term vs) -> Term vs -> Maybe (List (Nat, Term vs))
mkSubsts i specs [] rhs = Just []
mkSubsts i specs (arg :: args) rhs
    = do subs <- mkSubsts (1 + i) specs args rhs
         case lookup i specs of
              Nothing => Just subs
              Just tm => case arg of
                              Local _ _ idx _ =>
                                   Just ((idx, embed tm) :: subs)
                              As _ _ (Local _ _ idx1 _) (Local _ _ idx2 _) =>
                                   Just ((idx1, embed tm) :: (idx2, embed tm) :: subs)
                              As _ _ _ (Local _ _ idx _) =>
                                   Just ((idx, embed tm) :: subs)
                              _ => Nothing

-- In the case where all the specialised positions are variables on the LHS,
-- substitute the term in on the RHS
specPatByVar : List (Nat, Term [<]) ->
                (vs ** (Env Term vs, Term vs, Term vs)) ->
                Maybe (vs ** (Env Term vs, Term vs, Term vs))
specPatByVar specs (vs ** (env, lhs, rhs))
    = do let (fn, args) = getFnArgs lhs
         psubs <- mkSubsts 0 specs args rhs
         let lhs' = apply (getLoc fn) fn args
         pure (vs ** (env, substLocs psubs lhs', substLocs psubs rhs))

specByVar : List (Nat, Term [<]) ->
            List (vs ** (Env Term vs, Term vs, Term vs)) ->
            Maybe (List (vs ** (Env Term vs, Term vs, Term vs)))
specByVar specs [] = pure []
specByVar specs (p :: ps)
    = do p' <- specPatByVar specs p
         ps' <- specByVar specs ps
         pure (p' :: ps')

dropSpec : Nat -> List (Nat, ClosedTerm) -> List a -> List a
dropSpec i sargs [] = []
dropSpec i sargs (x :: xs)
    = case lookup i sargs of
           Nothing => x :: dropSpec (1 + i) sargs xs
           Just _ => dropSpec (1 + i) sargs xs

getSpecPats : {auto c : Ref Ctxt Defs} ->
              FC -> Name ->
              (fn : Name) -> (stk : List (FC, Term vars)) ->
              NF [<] -> -- Type of 'fn'
              List (Nat, ArgMode) -> -- All the arguments
              List (Nat, Term [<]) -> -- Just the static ones
              List (vs ** (Env Term vs, Term vs, Term vs)) ->
              Core (Maybe (List ImpClause))
getSpecPats fc pename fn stk fnty args sargs pats
   = do -- First, see if all the specialised positions are variables. If so,
        -- substitute the arguments directly into the RHS
        let Nothing = specByVar sargs pats
            | Just specpats =>
                   do ps <- traverse (unelabPat pename) specpats
                      pure (Just ps)
        -- Otherwise, build a new definition by taking the remaining arguments
        -- on the lhs, and using the specialised function application on the rhs.
        -- Then, this will get evaluated on elaboration.
        let dynnames = mkDynNames 0 args
        let lhs = apply (IVar fc pename) (map (IBindVar fc) dynnames)
        rhs <- mkRHSargs fnty (IVar fc fn) dynnames args
        pure (Just [PatClause fc lhs rhs])
  where
    mkDynNames : Int -> List (Nat, ArgMode) -> List String
    mkDynNames i [] = []
    mkDynNames i ((_, Dynamic) :: as)
        = ("_pe" ++ show i) :: mkDynNames (1 + i) as
    mkDynNames i (_ :: as) = mkDynNames i as

    -- Build a RHS from the type of the function to be specialised, the
    -- dynamic argument names, and the list of given arguments. We assume
    -- the latter two correspond appropriately.
    mkRHSargs : NF [<] -> RawImp -> List String -> List (Nat, ArgMode) ->
                Core RawImp
    mkRHSargs (NBind _ x (Pi _ _ Explicit _) sc) app (a :: as) ((_, Dynamic) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [<] (Erased fc Placeholder))
             mkRHSargs sc' (IApp fc app (IVar fc (UN $ Basic a))) as ds
    mkRHSargs (NBind _ x (Pi _ _ _ _) sc) app (a :: as) ((_, Dynamic) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [<] (Erased fc Placeholder))
             mkRHSargs sc' (INamedApp fc app x (IVar fc (UN $ Basic a))) as ds
    mkRHSargs (NBind _ x (Pi _ _ Explicit _) sc) app as ((_, Static tm) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [<] (Erased fc Placeholder))
             tm' <- unelabNoSugar [<] tm
             mkRHSargs sc' (IApp fc app (map rawName tm')) as ds
    mkRHSargs (NBind _ x (Pi _ _ Implicit _) sc) app as ((_, Static tm) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [<] (Erased fc Placeholder))
             tm' <- unelabNoSugar [<] tm
             mkRHSargs sc' (INamedApp fc app x (map rawName tm')) as ds
    mkRHSargs (NBind _ _ (Pi _ _ AutoImplicit _) sc) app as ((_, Static tm) :: ds)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts [<] (Erased fc Placeholder))
             tm' <- unelabNoSugar [<] tm
             mkRHSargs sc' (IAutoApp fc app (map rawName tm')) as ds
    -- Type will depend on the value here (we assume a variadic function) but
    -- the argument names are still needed
    mkRHSargs ty app (a :: as) ((_, Dynamic) :: ds)
        = mkRHSargs ty (IApp fc app (IVar fc (UN $ Basic a))) as ds
    mkRHSargs _ app _ _
        = pure app

    getRawArgs : List (Arg' Name) -> RawImp -> List (Arg' Name)
    getRawArgs args (IApp fc f arg) = getRawArgs (Explicit fc arg :: args) f
    getRawArgs args (INamedApp fc f n arg)
        = getRawArgs (Named fc n arg :: args) f
    getRawArgs args (IAutoApp fc f arg)
        = getRawArgs (Auto fc arg :: args) f
    getRawArgs args tm = args

    reapply : RawImp -> List (Arg' Name) -> RawImp
    reapply f [] = f
    reapply f (Explicit fc arg :: args) = reapply (IApp fc f arg) args
    reapply f (Named fc n arg :: args)
        = reapply (INamedApp fc f n arg) args
    reapply f (Auto fc arg :: args)
        = reapply (IAutoApp fc f arg) args

    dropArgs : Name -> RawImp -> RawImp
    dropArgs pename tm = reapply (IVar fc pename) (dropSpec 0 sargs (getRawArgs [] tm))

    unelabPat : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabPat pename (_ ** (env, lhs, rhs))
        = do logTerm "specialise" 20 "Unelaborating LHS:" lhs
             lhsapp <- unelabNoSugar env lhs
             log "specialise" 20 $ "Unelaborating LHS to: \{show lhsapp}"
             let lhs' = dropArgs pename (map rawName lhsapp)
             defs <- get Ctxt
             rhs <- normaliseArgHoles defs env rhs
             rhs <- unelabNoSugar env rhs
             let rhs = flip mapTTImp rhs $ \case
                      IHole fc _ => Implicit fc False
                      tm => tm
             pure (PatClause fc lhs' (map rawName rhs))

    unelabLHS : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core RawImp
    unelabLHS pename (_ ** (env, lhs, rhs))
        = do lhsapp <- unelabNoSugar env lhs
             pure $ dropArgs pename (map rawName lhsapp)

-- Get the reducible names in a function to be partially evaluated. In practice,
-- that's all the functions it refers to
-- TODO: May want to take care with 'partial' names?
getReducible : List Name -> -- calls to check
               NameMap Nat -> -- which nodes have been visited. If the entry is
                              -- present, it's visited
               Defs -> Core (NameMap Nat)
getReducible [] refs defs = pure refs
getReducible (n :: rest) refs defs
  = do let Nothing = lookup n refs
           | Just _ => getReducible rest refs defs
       case !(lookupCtxtExact n (gamma defs)) of
            Nothing => getReducible rest refs defs
            Just def =>
              do let refs' = insert n 65536 refs
                 let calls = refersTo def
                 getReducible (keys calls ++ rest) refs' defs

mkSpecDef : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> GlobalDef ->
            Name -> List (Nat, ArgMode) -> Name -> List (FC, Term vars) ->
            Core (Term vars)
mkSpecDef {vars} fc gdef pename sargs fn stk
    = handleUnify {unResolve = True}
       (do defs <- get Ctxt
           setAllPublic True
           let staticargs
                 = mapMaybe (\ (x, s) => case s of
                                              Dynamic => Nothing
                                              Static t => Just (x, t)) sargs
           let peapp = applyStackWithFC (Ref fc Func pename) (dropSpec 0 staticargs stk)
           Nothing <- lookupCtxtExact pename (gamma defs)
               | Just _ => -- already specialised
                           do log "specialise" 5 $ "Already specialised " ++ show pename
                              pure peapp
           logC "specialise.declare" 5 $
                   do fnfull <- toFullNames fn
                      args' <- traverse (\ (i, arg) =>
                                   do arg' <- the (Core ArgMode) $ case arg of
                                                   Static a =>
                                                      pure $ Static !(toFullNames a)
                                                   Dynamic => pure Dynamic
                                      pure (show (i, arg'))) sargs
                      pure $ "Specialising " ++ show fnfull ++
                             " (" ++ show fn ++ ") -> \{show pename} by " ++
                             showSep ", " args'
           let sty = specialiseTy 0 staticargs (type gdef)
           logTermNF "specialise" 3 ("Specialised type " ++ show pename) [<] sty

           -- Add as RigW - if it's something else, we don't need it at
           -- runtime anyway so this is wasted effort, therefore a failure
           -- is okay!
           let defflags := propagateFlags (flags gdef)
           log "specialise.flags" 20 "Defining \{show pename} with flags: \{show defflags}"
           peidx <- addDef pename
                  $ the (GlobalDef -> GlobalDef) { flags := defflags }
                  $ newDef fc pename top [<] sty (specified Public) None
           addToSave (Resolved peidx)

           -- Reduce the function to be specialised, and reduce any name in
           -- the arguments at most once (so that recursive definitions aren't
           -- unfolded forever)
           let specnames = getAllRefs empty (map snd sargs)
           specLimits <- traverse (\n => pure (n, 1))
                                  (keys specnames)

           defs <- get Ctxt
           reds <- getReducible [fn] empty defs
           setFlag fc (Resolved peidx) (PartialEval (specLimits ++ toList reds))

           let PMDef pminfo pmargs ct tr pats = definition gdef
               | _ => pure (applyStackWithFC (Ref fc Func fn) stk)
           logC "specialise" 5 $
                   do inpats <- traverse unelabDef pats
                      pure $ "Attempting to specialise:\n" ++
                             showSep "\n" (map showPat inpats)

           Just newpats <- getSpecPats fc pename fn stk !(nf defs [<] (type gdef))
                                       sargs staticargs pats
                | Nothing => pure (applyStackWithFC (Ref fc Func fn) stk)
           log "specialise" 5 $ "New patterns for " ++ show pename ++ ":\n" ++
                    showSep "\n" (map showPat newpats)
           processDecl [InPartialEval] (MkNested []) [<]
                       (IDef fc (Resolved peidx) newpats)
           setAllPublic False
           pure peapp)
           -- If the partially evaluated definition fails, just use the initial
           -- application. It might indicates a bug in the P.E. function generation
           -- if it fails, but I don't want the whole system to be dependent on
           -- the correctness of PE!
        (\err =>
           do logC "specialise.fail" 1 $ do
                 fn <- toFullNames fn
                 pure "Partial evaluation of \{show fn} failed:\n\{show err}"
              update Ctxt { peFailures $= insert pename () }
              pure (applyStackWithFC (Ref fc Func fn) stk))
  where

    identityFlag : List (Nat, ArgMode) -> Nat -> Maybe Nat
    identityFlag [] k = pure k
    identityFlag ((pos, mode) :: sargs) k
      = k <$ guard (k < pos)
      <|> (case mode of { Static _ => (`minus` 1); Dynamic => id }) <$> identityFlag sargs k


    propagateFlags : List DefFlag -> List DefFlag
    propagateFlags = mapMaybe $ \case
      Deprecate => Nothing
      Overloadable => Nothing
      Identity k => Identity <$> identityFlag sargs k
      fl => Just fl

    getAllRefs : NameMap Bool -> List ArgMode -> NameMap Bool
    getAllRefs ns (Dynamic :: xs) = getAllRefs ns xs
    getAllRefs ns (Static t :: xs)
        = addRefs False (UN Underscore) (getAllRefs ns xs) t
    getAllRefs ns [] = ns

    updateApp : Name -> RawImp -> RawImp
    updateApp n (IApp fc f a) = IApp fc (updateApp n f) a
    updateApp n (IAutoApp fc f a) = IAutoApp fc (updateApp n f) a
    updateApp n (INamedApp fc f m a) = INamedApp fc (updateApp n f) m a
    updateApp n f = IVar fc n

    unelabDef : (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabDef (_ ** (env, lhs, rhs))
        = do lhs' <- unelabNoSugar env lhs
             defs <- get Ctxt
             rhsnf <- normaliseArgHoles defs env rhs
             rhs' <- unelabNoSugar env rhsnf
             pure (PatClause fc (map rawName lhs') (map rawName rhs'))

    showPat : ImpClause -> String
    showPat (PatClause _ lhs rhs) = show lhs ++ " = " ++ show rhs
    showPat _ = "Can't happen"

eraseInferred : {auto c : Ref Ctxt Defs} ->
                Term vars -> Core (Term vars)
eraseInferred (Bind fc x b tm)
    = do b' <- traverse eraseInferred b
         tm' <- eraseInferred tm
         pure (Bind fc x b' tm')
eraseInferred tm
    = case getFnArgs tm of
           (f, []) => pure f
           (Ref fc Func n, args) =>
                do defs <- get Ctxt
                   Just gdef <- lookupCtxtExact n (gamma defs)
                        | Nothing => pure tm
                   let argsE = dropErased fc 0 (inferrable gdef) args
                   argsE' <- traverse eraseInferred argsE
                   pure (apply fc (Ref fc Func n) argsE')
           (f, args) =>
                do args' <- traverse eraseInferred args
                   pure (apply (getLoc f) f args)
  where
    dropErased : FC -> Nat -> List Nat -> List (Term vars) -> List (Term vars)
    dropErased fc pos ps [] = []
    dropErased fc pos ps (n :: ns)
        = if pos `elem` ps
             then Erased fc Placeholder :: dropErased fc (1 + pos) ps ns
             else n :: dropErased fc (1 + pos) ps ns

-- Specialise a function name according to arguments. Return the specialised
-- application on success, or Nothing if it's not specialisable (due to static
-- arguments not being concrete)
specialise : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             FC -> Env Term vars -> GlobalDef ->
             Name -> List (FC, Term vars) ->
             Core (Maybe (Term vars))
specialise {vars} fc env gdef fn stk
    = case specArgs gdef of
        [] => pure Nothing
        specs =>
            do fnfull <- toFullNames fn
               -- If all the arguments are concrete (meaning, no local variables
               -- or holes in them, so they can be a Term [<]) we can specialise
               Just sargs <- getSpecArgs 0 specs stk
                   | Nothing => pure Nothing
               defs <- get Ctxt
               sargs <- for sargs $ traversePair $ traverseArgMode $ \ tm =>
                          normalise defs [<] tm
               let nhash = hash !(traverse toFullNames $ mapMaybe getStatic $ map snd sargs)
                              `hashWithSalt` fnfull -- add function name to hash to avoid namespace clashes
               let pename = NS partialEvalNS
                            (UN $ Basic ("PE_" ++ nameRoot fnfull ++ "_" ++ asHex (cast nhash)))
               defs <- get Ctxt
               case lookup pename (peFailures defs) of
                    Nothing => Just <$> mkSpecDef fc gdef pename sargs fn stk
                    Just _ => pure Nothing
  where
    concrete : {vars : _} ->
               Term vars -> Maybe (Term [<])
    concrete tm = shrink tm none

    getSpecArgs : Nat -> List Nat -> List (FC, Term vars) ->
                  Core (Maybe (List (Nat, ArgMode)))
    getSpecArgs i specs [] = pure (Just [])
    getSpecArgs i specs ((_, x) :: xs)
        = do Just xs' <- getSpecArgs (1 + i) specs xs
                 | Nothing => pure Nothing
             if i `elem` specs
                then do defs <- get Ctxt
                        x' <- normaliseHoles defs env x
                        x' <- eraseInferred x'
                        let Just xok = concrete x'
                            | Nothing => pure Nothing
                        pure $ Just ((i, Static xok) :: xs')
                else pure $ Just ((i, Dynamic) :: xs')

findSpecs : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            Env Term vars -> List (FC, Term vars) -> Term vars ->
            Core (Term vars)
findSpecs env stk (Ref fc Func fn)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | Nothing => pure (applyStackWithFC (Ref fc Func fn) stk)
         Just r <- specialise fc env gdef fn stk
              | Nothing => pure (applyStackWithFC (Ref fc Func fn) stk)
         pure r
findSpecs env stk (Meta fc n i args)
    = do args' <- traverse (findSpecs env []) args
         pure $ applyStackWithFC (Meta fc n i args') stk
findSpecs env stk (Bind fc x b sc)
    = do b' <- traverse (findSpecs env []) b
         sc' <- findSpecs (env :< b') [] sc
         pure $ applyStackWithFC (Bind fc x b' sc') stk
findSpecs env stk (App fc fn arg)
    = do arg' <- findSpecs env [] arg
         findSpecs env ((fc, arg') :: stk) fn
findSpecs env stk (TDelayed fc r tm)
    = do tm' <- findSpecs env [] tm
         pure $ applyStackWithFC (TDelayed fc r tm') stk
findSpecs env stk (TDelay fc r ty tm)
    = do ty' <- findSpecs env [] ty
         tm' <- findSpecs env [] tm
         pure $ applyStackWithFC (TDelay fc r ty' tm') stk
findSpecs env stk (TForce fc r tm)
    = do tm' <- findSpecs env [] tm
         pure $ applyStackWithFC (TForce fc r tm') stk
findSpecs env stk tm = pure $ applyStackWithFC tm stk

bName : {auto q : Ref QVar Int} -> String -> Core Name
bName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

-- This is like 'quote' in 'Normalise', except that when we encounter a
-- function name we need to check whether to specialise.
-- (Sorry about all the repetition - I don't really want to export those
-- internal details, and there is a small but crucial change where we call
-- quoteHead as compared with the version in Core.Normalise, to deal with
-- checking for specialised applications.)
mutual
  quoteArgs : {bound, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> SnocList (Closure free) ->
              Core (SnocList (Term (free ++ bound)))
  quoteArgs q defs bounds env [<] = pure [<]
  quoteArgs q defs bounds env (args :< a)
      = pure $ (!(quoteArgs q defs bounds env args) :<
                !(quoteGenNF q defs bounds env !(evalClosure defs a)))

  quoteArgsWithFC : {auto c : Ref Ctxt Defs} ->
                    {auto m : Ref MD Metadata} ->
                    {auto u : Ref UST UState} ->
                    {auto s : Ref Syn SyntaxInfo} ->
                    {auto o : Ref ROpts REPLOpts} ->
                    {bound, free : _} ->
                    Ref QVar Int -> Defs -> Bounds bound ->
                    Env Term free -> SnocList (FC, Closure free) ->
                    Core (SnocList (FC, Term (free ++ bound)))
  quoteArgsWithFC q defs bounds env terms
      = pure $ zip (map fst terms) !(quoteArgs q defs bounds env (map snd terms))

  quoteHead : {bound, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              Ref QVar Int -> Defs ->
              FC -> Bounds bound -> Env Term free -> NHead free ->
              Core (Term (free ++ bound))
  quoteHead {bound} q defs fc bounds env (NLocal mrig _ prf)
      = let MkVar prf' = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : {idx : _} -> (ys : SnocList Name) -> (0 p : IsVar n idx xs) ->
                 Var (xs ++ ys)
      addLater [<] isv = MkVar isv
      addLater (xs :< x) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs fc bounds env (NRef Bound (MN n i))
      = case findName bounds of
             Just (MkVar p) => pure $ Local fc Nothing _ (embedIsVar p)
             Nothing => pure $ Ref fc Bound (MN n i)
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
  quoteHead q defs fc bounds env (NRef nt n) = pure $ Ref fc nt n
  quoteHead q defs fc bounds env (NMeta n i args)
      = do args' <- quoteArgs q defs bounds env (map snd args)
           -- See [Note] Meta args
           pure $ Meta fc n i (toList $ args')

  quotePi : {bound, free : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            Ref QVar Int -> Defs -> Bounds bound ->
            Env Term free -> PiInfo (Closure free) ->
            Core (PiInfo (Term (free ++ bound)))
  quotePi q defs bounds env Explicit = pure Explicit
  quotePi q defs bounds env Implicit = pure Implicit
  quotePi q defs bounds env AutoImplicit = pure AutoImplicit
  quotePi q defs bounds env (DefImplicit t)
      = do t' <- quoteGenNF q defs bounds env !(evalClosure defs t)
           pure (DefImplicit t')

  quoteBinder : {bound, free : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                Ref QVar Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (Closure free) ->
                Core (Binder (Term (free ++ bound)))
  quoteBinder q defs bounds env (Lam fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           p' <- quotePi q defs bounds env p
           pure (Lam fc r p' ty')
  quoteBinder q defs bounds env (Let fc r val ty)
      = do val' <- quoteGenNF q defs bounds env !(evalClosure defs val)
           ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (Let fc r val' ty')
  quoteBinder q defs bounds env (Pi fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           p' <- quotePi q defs bounds env p
           pure (Pi fc r p' ty')
  quoteBinder q defs bounds env (PVar fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           p' <- quotePi q defs bounds env p
           pure (PVar fc r p' ty')
  quoteBinder q defs bounds env (PLet fc r val ty)
      = do val' <- quoteGenNF q defs bounds env !(evalClosure defs val)
           ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (PLet fc r val' ty')
  quoteBinder q defs bounds env (PVTy fc r ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (PVTy fc r ty')

  quoteGenNF : {bound, vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               Ref QVar Int ->
               Defs -> Bounds bound ->
               Env Term vars -> NF vars -> Core (Term (vars ++ bound))
  quoteGenNF q defs bound env (NBind fc n b sc)
      = do var <- bName "qv"
           sc' <- quoteGenNF q defs (Add n var bound) env
                       !(sc defs (toClosure defaultOpts env (Ref fc Bound var)))
           b' <- quoteBinder q defs bound env b
           pure (Bind fc n b' sc')
  -- IMPORTANT CASE HERE
  -- If fn is to be specialised, quote the args directly (no further
  -- reduction) then call specialise. Otherwise, quote as normal
  quoteGenNF q defs bound env (NApp fc (NRef Func fn) args)
      = do Just gdef <- lookupCtxtExact fn (gamma defs)
                | Nothing => do args' <- quoteArgsWithFC q defs bound env args
                                pure $ applySpineWithFC (Ref fc Func fn) args'
           case specArgs gdef of
                [] => do args' <- quoteArgsWithFC q defs bound env args
                         pure $ applySpineWithFC (Ref fc Func fn) args'
                _ => do empty <- clearDefs defs
                        args' <- quoteArgsWithFC q defs bound env args
                        Just r <- specialise fc (extendEnv bound env) gdef fn (toList args')
                             | Nothing =>
                                  -- can't specialise, keep the arguments
                                  -- unreduced
                                  do args' <- quoteArgsWithFC q empty bound env args
                                     pure $ applySpineWithFC (Ref fc Func fn) args'
                        pure r
     where
       extendEnv : Bounds bs -> Env Term vs -> Env Term (vs ++ bs)
       extendEnv None env = env
       extendEnv (Add x n bs) env
           -- We're just using this to evaluate holes in the right scope, so
           -- a placeholder binder is fine
           = extendEnv bs env :< Lam fc top Explicit (Erased fc Placeholder)
  quoteGenNF q defs bound env (NApp fc f args)
      = do f' <- quoteHead q defs fc bound env f
           args' <- quoteArgsWithFC q defs bound env args
           pure $ applySpineWithFC f' args'
  quoteGenNF q defs bound env (NDCon fc n t ar args)
      = do args' <- quoteArgsWithFC q defs bound env args
           pure $ applySpineWithFC (Ref fc (DataCon t ar) n) args'
  quoteGenNF q defs bound env (NTCon fc n t ar args)
      = do args' <- quoteArgsWithFC q defs bound env args
           pure $ applySpineWithFC (Ref fc (TyCon t ar) n) args'
  quoteGenNF q defs bound env (NAs fc s n pat)
      = do n' <- quoteGenNF q defs bound env n
           pat' <- quoteGenNF q defs bound env pat
           pure (As fc s n' pat')
  quoteGenNF q defs bound env (NDelayed fc r arg)
      = do argQ <- quoteGenNF q defs bound env arg
           pure (TDelayed fc r argQ)
  quoteGenNF q defs bound env (NDelay fc r ty arg)
      -- unlike main evaluator, we want to look under Delays
      = do argNF <- evalClosure defs arg
           argQ <- quoteGenNF q defs bound env argNF
           tyNF <- evalClosure defs ty
           tyQ <- quoteGenNF q defs bound env tyNF
           pure (TDelay fc r tyQ argQ)
    where
      toHolesOnly : Closure vs -> Closure vs
      toHolesOnly (MkClosure _ locs env tm)
          = MkClosure withHoles locs env tm
      toHolesOnly c = c
  quoteGenNF q defs bound env (NForce fc r arg args)
      = do args' <- quoteArgsWithFC q defs bound env args
           case arg of
                NDelay fc _ _ arg =>
                   do argNF <- evalClosure defs arg
                      pure $ applySpineWithFC !(quoteGenNF q defs bound env argNF) args'
                _ => do arg' <- quoteGenNF q defs bound env arg
                        pure $ applySpineWithFC (TForce fc r arg') args'
  quoteGenNF q defs bound env (NPrimVal fc c) = pure $ PrimVal fc c
  quoteGenNF q defs bound env (NErased fc Impossible) = pure $ Erased fc Impossible
  quoteGenNF q defs bound env (NErased fc Placeholder) = pure $ Erased fc Placeholder
  quoteGenNF q defs bound env (NErased fc (Dotted t))
    = pure $ Erased fc $ Dotted !(quoteGenNF q defs bound env t)
  quoteGenNF q defs bound env (NType fc u) = pure $ TType fc u

evalRHS : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          Env Term vars -> NF vars -> Core (Term vars)
evalRHS env nf
    = do q <- newRef QVar 0
         defs <- get Ctxt
         quoteGenNF q defs None env nf

export
applySpecialise : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  Env Term vars ->
                  Maybe (List (Name, Nat)) ->
                        -- ^ If we're specialising, names to reduce in the RHS
                        -- with their reduction limits
                  Term vars -> -- initial RHS
                  Core (Term vars)
applySpecialise env Nothing tm
    = findSpecs env [] tm -- not specialising, just search through RHS
applySpecialise env (Just ls) tmin -- specialising, evaluate RHS while looking
                                 -- for names to specialise
    = do defs <- get Ctxt
         tm <- toResolvedNames tmin
         nf <- nf defs env tm
         tm' <- evalRHS env nf
         tmfull <- toFullNames tm'
         logTermNF "specialise" 5 ("New RHS") env tmfull
         pure tmfull
