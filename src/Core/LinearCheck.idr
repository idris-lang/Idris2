module Core.LinearCheck

-- Linearity checking of already typechecked/elaborated terms
-- Assumption: Terms are already type correct and we're only checking usage.
-- of local variables.
-- We must be able to complete linearity checking without reference to the
-- global context, although we are allowed to accuess the global context to
-- update quantities in hold types.

import Core.Context.Log
import Core.Env
import Core.Evaluate

import Data.SnocList
import Data.Vect
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.VarSet.Core as VarSet

%default covering

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
Usage : Scoped
Usage vars = SnocList (Var vars)

namespace Usage
  public export
  empty : Usage vars
  empty = [<]

  public export
  single : Var vars -> Usage vars
  single a = [<a]

record HoleApp vars where
  constructor MkHoleApp
  resolvedName : Int
  -- Scope the hole is applied to. This might be bigger than the scope we're
  -- currently in, so we may not know about some arguments. That's okay,
  -- because we're only updating usage of the things we know about
  scope : List (Maybe (Term vars))

{vars: _} -> Show (HoleApp vars) where
  show (MkHoleApp resolvedName scope) = "HoleApp { resolvedName=\{show resolvedName} scope=\{assert_total $ show scope} }"

-- A tree, built from the term, explaining what is used where.
-- We need this because of the interaction between case branches and holes.
-- If a variable is used in one branch, but not in another, then holes in
-- each branch need to respect the usage information.
-- However, we also need to know usage in the rest of the term before we
-- can update holes accurately
record HoleUsage vars where
  constructor HUsage
  location : FC
  used : Usage vars
  caseAlts : List (HoleUsage vars)
  holeApps : List (HoleApp vars)

{vars: _} -> Show (HoleUsage vars) where
  show (HUsage location used caseAlts holeApps) = "HUsage { location=\{show location} used=\{show used} caseAlts=\{assert_total $ show caseAlts} holeApps=\{show holeApps} }"

hdone : FC -> Core (HoleUsage vars)
hdone fc = pure $ HUsage fc [<] [] []

-- We're finished with the scope of a binder, so forget about any uses of
-- the variable and any hole it's in
doneScope : HoleUsage (vars :< n) -> HoleUsage vars
doneScope (HUsage fc u hs apps)
    = HUsage fc (doneScopeU u) (map doneScope hs) (map doneScopeH apps)
  where
    doneScopeV : Var (vars :< n) -> Maybe (Var vars)
    doneScopeV (MkVar First) = Nothing
    doneScopeV (MkVar (Later p)) = Just (MkVar p)

    doneScopeU : Usage (vars :< n) -> Usage vars
    doneScopeU [<] = [<]
    doneScopeU (xs :< v)
       = maybe (doneScopeU xs) (\v' => doneScopeU xs :< v')
               (doneScopeV v)

    doneScopeH : HoleApp (vars :< n) -> HoleApp vars
    doneScopeH app
        = let scope' = map (maybe Nothing
                                (\tm => shrinkTerm tm (Drop Refl)))
                           (scope app) in
              ({ scope := scope' } app)

combine : FC -> HoleUsage ns -> HoleUsage ns -> HoleUsage ns
-- Doesn't matter where things appear, other than in alternatives, so
-- just concatenate
combine fc (HUsage _ us alts apps) (HUsage _ us' alts' apps')
    = HUsage fc (us ++ us') (alts ++ alts') (apps ++ apps')

concat : FC -> List (HoleUsage ns) -> HoleUsage ns
concat fc [] = HUsage fc [<] [] []
concat fc [u] = u
concat fc (u :: us) = combine fc u (concat fc us)

-- Count the definite uses in the scope
countU : Nat -> Usage ns -> Nat
countU p [<] = 0
countU p (xs :< v)
    = if p == varIdx v then 1 + countU p xs else countU p xs

count : Nat -> HoleUsage ns -> Nat
count n (HUsage _ us _ _) = countU n us

getIdxs : {ns : _} -> Usage ns -> List Nat
getIdxs [<] = []
getIdxs (vs :< v) = varIdx v :: getIdxs vs

sameUsage : {ns : _} -> Usage ns -> Usage ns -> Bool
sameUsage xs ys = sort (getIdxs xs) == sort (getIdxs ys)

allSameUsage : {ns : _} -> List (HoleUsage ns) -> Maybe (HoleUsage ns)
allSameUsage [] = Just (HUsage EmptyFC [<] [] [])
allSameUsage [u] = Just u
allSameUsage (u :: v :: vs)
    = if sameUsage (used u) (used v)
         then allSameUsage (v :: vs)
         else Nothing

anyHoles : HoleUsage vars -> Bool
anyHoles (HUsage _ _ alts []) = or (map (\x => Delay x) (map anyHoles alts))
anyHoles (HUsage _ _ _ (_ :: _)) = True

smallerU : List Nat -> List Nat -> Bool
smallerU [] xs = True
smallerU (x :: xs) (y :: ys)
    = if x == y
         then smallerU xs ys
         else smallerU (x :: xs) ys
smallerU _ _ = False

-- Check whether the first usage set is smaller than the second, and contains
-- holes.
smaller : {vars : _} -> HoleUsage vars -> HoleUsage vars -> Bool
smaller u v
    = sameUsage (used u) (used v) ||
         (anyHoles u &&
            smallerU (sort (getIdxs (used u))) (sort (getIdxs (used v))))

getNames : {vars : _} -> Usage vars -> List Name
getNames [<] = []
getNames (ns :< MkVar p) = nameAt p :: getNames ns

compatibleWith : {vars : _} ->
                 FC -> HoleUsage vars -> List (HoleUsage vars) -> Core (Usage vars)
compatibleWith fc u [] = pure (used u)
compatibleWith fc u (v :: vs)
    = if smaller u v
         then compatibleWith fc u vs
         else if smaller v u
                 then compatibleWith fc v vs
                 else throw (InconsistentUse fc [(location u, getNames (used u)),
                                                 (location v, getNames (used v))])

compatibleUsage : {vars : _} ->
                  FC -> List (HoleUsage vars) -> Core (Usage vars)
compatibleUsage fc [] = pure [<]
compatibleUsage fc [u] = pure (used u)
compatibleUsage fc (u :: v :: us) = compatibleWith fc u (v :: us)

localPrf : {n : Name} -> {vars, later: Scope} -> Var (vars :< n ++ later)
localPrf {later = [<]} = MkVar First
localPrf {n} {vars} {later = (xs :< x)}
    = let MkVar p = localPrf {n} {vars} {later = xs} in
          MkVar (Later p)

parameters {auto c : Ref Ctxt Defs}
  -- The assumption here is that hole types are abstracted over the entire
  -- environment, so that they have the appropriate number of function
  -- arguments and there are no lets
  updateHoleType : {vars : _} ->
                    (useInHole : Bool) ->
                    Var vars ->
                    VarSet vars ->
                    Term vs -> List (Maybe (Term vars)) ->
                    Core (Term vs)
  updateHoleType useInHole var zs (Bind bfc nm (Pi fc' c e ty) sc) (Just (Local _ _ v _) :: as)
      -- if the argument to the hole type is the variable of interest,
      -- and the variable should be used in the hole, leave multiplicity alone,
      -- otherwise set it to erased
      = if varIdx var == v
           then do scty <- updateHoleType False var zs sc as
                   let c' = if useInHole then c else erased
                   pure (Bind bfc nm (Pi fc' c' e ty) scty)
           else if VarSet.elemNat v zs
               then do scty <- updateHoleType useInHole var zs sc as
                       pure (Bind bfc nm (Pi fc' erased e ty) scty)
               else do scty <- updateHoleType useInHole var zs sc as
                       pure (Bind bfc nm (Pi fc' c e ty) scty)
  updateHoleType useInHole var zs (Bind bfc nm b@(Pi fc' c e ty) sc) (_ :: as)
      = do scty <- updateHoleType useInHole var zs sc as
           pure (Bind bfc nm b scty)
  updateHoleType useInHole var zs ty as
      = pure ty

  updateHoleApp : {vars : _} ->
                  (useInHole : Bool) -> Var vars -> VarSet vars ->
                  HoleApp vars -> Core ()
  updateHoleApp useInHole v zs hole
      = do defs <- get Ctxt
           let i = resolvedName hole
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
               | Nothing => pure ()
           case definition gdef of
               Hole {} =>
                  do let ty = type gdef
                     ty' <- updateHoleType useInHole v zs ty (scope hole)
                     updateTy i ty'
                     logTerm "quantity.hole.update" 5 ("New type of " ++
                               show (fullname gdef)) ty'
                     logTerm "quantity.hole.update" 5 ("Updated from " ++
                               show (fullname gdef)) (type gdef)
               _ => pure ()

  -- For all the holes in the usage tree update their type so that
  -- the variable in question's usage is set appropriately. If it appears
  -- in the current known usage list, -- set its multiplicity to zero.
  -- This is so that, in interactive editing, a user can see whether a variable
  -- is available for usage in a hole or not.
  updateHoleUsage : {vars : _} ->
                    Var vars -> -- Variable in question
                    VarSet vars -> -- erased variables in environment
                    Usage vars -> -- Complete usage so far
                    HoleUsage vars -> Core Bool
  updateHoleUsage var@(MkVar {varIdx} _) zs usage (HUsage fc moreUsage alts holes)
      = do let usage = usage ++ moreUsage
           let used = countU varIdx usage == 0
           anyHoles <- traverse (updateHoleUsage var zs usage) alts
           traverse_ (updateHoleApp used var zs) holes
           pure (not (null holes) || or (map (\x => Delay x) anyHoles))

  lcheck : {vars : _} ->
           RigCount -> Env Term vars -> Term vars ->
           Core (HoleUsage vars)

  -- Checking if the bound variable is used appropriately in the scope
  checkUsageOK : FC -> Nat -> Name -> RigCount -> Core ()
  checkUsageOK fc used nm r
      = when (isLinear r && used /= 1)
          (do log "quantity" 5 $ "Linearity error " ++ show nm
              throw (LinearUsed fc used nm))

  -- Check if a term has holes (not under case alternatives, and not in types
  -- that are in multiplicity 0 anyway).
  -- This is so when we check linearity of case alternatives, we do the ones
  -- without holes first to establish what the correct usage should be
  hasHoles : Term vars -> Core Bool
  hasHoles (Meta _ _ i _)
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => pure False
           case definition gdef of
                Hole _ _ => pure True
                _ => pure False
  hasHoles (Bind _ _ b sc)
      = if !(hasHolesBinder b) then pure True
                               else hasHoles sc
    where
      hasHolesBinder : Binder (Term vars) -> Core Bool
      hasHolesBinder (Let _ _ val _) = hasHoles val
      hasHolesBinder _ = pure False
  hasHoles (App _ f _ a)
      = if !(hasHoles f) then pure True else hasHoles a
  hasHoles (Case _ _ _ sc _ _) = hasHoles sc
  hasHoles (TDelay _ _ _ tm) = hasHoles tm
  hasHoles (TForce _ _ tm) = hasHoles tm
  hasHoles _ = pure False

  -- Check a case alternative. Returns the usage tree just for that alternative
  lcheckAlt : {vars : _} ->
              -- must be Rig0 or Rig1
              (rhsrig : RigCount) ->
              Env Term vars ->
              (scrig : RigCount) ->
              CaseAlt vars ->
              Core (HoleUsage vars)
  lcheckAlt rig env scrig (ConCase fc n t sc)
      = lcheckScope env sc
    where
      lcheckScope : {vars : _} -> Env Term vars -> CaseScope vars ->
                    Core (HoleUsage vars)
      lcheckScope env (RHS _ tm)
          = lcheck rig env tm
      lcheckScope env (Arg c x sc)
            -- We don't have the type of the argument, but the good news is
            -- that we don't need it because we only need multiplicities and
            -- they are cached in App nodes.
          = do let env'
                   = env :<
                     PVar fc (rigMult scrig c) Explicit (Erased fc Placeholder)
               usc <- lcheckScope env' sc
               let used_in = count 0 usc
               -- As with binders, check for holes in the scope and update
               -- their types if this variable has been consumed linearly
               holeFound <- if isLinear c
                               then updateHoleUsage
                                             (MkVar First)
                                             (weaken @{varSetWeaken} (getErased env))
                                             [<]
                                             usc
                               else pure False
               let used = if isLinear (rigMult c rig) &&
                             holeFound && used_in == 0
                             then 1
                             else used_in
               checkUsageOK EmptyFC used x (rigMult (rigMult scrig c) rig)
               pure (doneScope usc)
  lcheckAlt rig env scrig (DelayCase fc t a rhs)
      = do -- See above for why the types are erased
           let env'
               = env :<
                 PVar fc erased Implicit (Erased fc Placeholder) :<
                 PVar fc scrig Explicit (Erased fc Placeholder)
           u' <- lcheck rig env' rhs
           -- t and a are not linear, so nothing to check
           pure (doneScope (doneScope u'))
  lcheckAlt rig env scrig (ConstCase fc c rhs)
      = lcheck rig env rhs
  lcheckAlt rig env scrig (DefaultCase fc rhs)
      = lcheck rig env rhs

  lcheckAlts : {vars : _} ->
               FC -> (rhsrig : RigCount) ->
               Env Term vars ->
               (scrig : RigCount) ->
               List (CaseAlt vars) ->
               Core (HoleUsage vars)
  lcheckAlts fc rig env scrig alts
      = do allUs <- traverse (lcheckAlt rig env scrig) alts
           -- If all the alternatives have the same usage, and there's no
           -- holes, just lift it out, because then we can count usages
           -- properly at the next level up
           if not (or (map (\x => Delay x) (map anyHoles allUs)))
              then do let Just u = allSameUsage allUs
                           | Nothing =>
                                throw (InconsistentUse fc (map getUse allUs))
                      pure u
              else
                   -- Otherwise, check the the usage is at least compatible
                   -- and build a tree for traversing by updateHoleUsage later
                   do us <- compatibleUsage fc allUs
                      pure (HUsage fc us allUs [])
    where
      getUse : {vars : _} -> HoleUsage vars -> (FC, List Name)
      getUse h = (location h, getNames (used h))

  lcheckBinder : {vars : _} ->
           RigCount -> Env Term vars -> Binder (Term vars) ->
           Core (HoleUsage vars)
  lcheckBinder rig env (Lam fc c p ty) = hdone fc
  lcheckBinder rig env (Let fc c val ty) = lcheck (rigMult rig c) env val
  lcheckBinder rig env (Pi fc c p ty) = lcheck (rigMult rig c) env ty
  lcheckBinder rig env (PVar fc c p ty) = hdone fc
  lcheckBinder rig env (PLet fc c val ty) = lcheck (rigMult rig c) env val
  lcheckBinder rig env (PVTy fc c ty) = hdone fc

  lcheck {vars} rig env (Local fc _ idx prf)
      = let b = getBinder prf env
            rigb = multiplicity b in
            do rigSafe rigb rig
               pure (HUsage fc (used (rigMult rig rigb)) [] [])
    where
      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe l r = when (l < r)
                         (throw (LinearMisuse fc (nameAt prf) l r))

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used r = if isLinear r then [<MkVar prf] else [<]
  lcheck rig env (Ref fc nt n)
      = do logC "quantity" 15 $ do pure "lcheck Ref \{show (nt)} \{show !(toFullNames n)}"
           hdone fc -- No quantity to check, and the name's quantity was checked
              -- when type checking
  lcheck {vars} rig env (Meta fc n i args)
      -- If the metavariable is defined, check as normal (we assume that
      -- quantities cached in the arguments have been set appropriately when
      -- the metavariable was resolved).
      -- Otherwise, don't count any usage in the 'args' - we'll update the
      -- type of the hole
      -- when we updateHoleUsage based on usages elsewhere, because we don't
      -- know if it's used until the hole is defined.
      = if isErased rig
           then hdone fc
           else
             do defs <- get Ctxt
                let defined
                      = case !(lookupCtxtExact (Resolved i) (gamma defs)) of
                             Nothing => False
                             Just def => case definition def of
                                              Function {} => True
                                              _ => False
                us <- logDepth $ traverse (\ (c, arg) => logDepth $ lcheck (rigMult rig c) env arg) args
                let newHoleApp : HoleApp vars
                    = MkHoleApp i (map (Just . snd) args)
                if defined
                   then pure (concat fc us)
                   else pure ({ used := [<],
                                holeApps $= (newHoleApp ::) } (concat fc us))
  lcheck rig_in env (Bind fc nm b sc)
      = do ub <- lcheckBinder rig env b

           -- Anything linear can't be used in the scope of a let/lambda, if
           -- we're checking in general context
           let (env', rig') = case b of
                                   Pi _ _ _ _ => (env, rig)
                                   _ => (restrictEnv env rig, presence rig)

           usc <- logDepth $ lcheck rig' (env' :< b) sc
           let used_in = count 0 usc

           -- Look for holes in the scope, if the variable is linearly bound.
           -- If the variable hasn't been used, we assume it is to be used in
           -- any holes in the scope of the binder (this is so when a user
           -- inspects the type, they see there is 1 usage available).
           -- 'updateHoleUsage' updates the type of any holes to reflect
           -- whether the variable in question is usable or not.
           holeFound <- if isLinear (multiplicity b)
                           then updateHoleUsage
                                         (MkVar First)
                                         (weaken @{varSetWeaken} (getErased env))
                                         [<]
                                         usc
                           else pure False

           -- The final usage count is always 1 if the bound variable is
           -- linear and there are holes. Otherwise, we take the count we
           -- found above.
           let used = if isLinear (rigMult (multiplicity b) rig') &&
                         holeFound && used_in == 0
                         then (S Z)
                         else used_in

           checkUsageOK fc used nm (rigMult (multiplicity b) rig')
           pure (combine fc ub (doneScope usc))
    where
      rig : RigCount
      rig = case b of
                 Pi {} =>
                      if isErased rig_in
                         then erased
                         else top -- checking as if an inspectable run-time type
                 _ => rig_in

  lcheck rig env (App fc fn q arg)
      = do logC "quantity" 15 $ do pure "lcheck App \{show !(toFullNames fn)} \{show !(toFullNames arg)}"
           uf <- logDepth $ lcheck rig env fn
           ua <- logDepth $ lcheck (rigMult rig q) env arg
           pure (combine fc uf ua)
  lcheck rig env (As fc s var pat)
      = lcheck rig env pat
  lcheck rig env (Case fc t scrig sc ty alts)
      = do usc <- logDepth $ lcheck (rigMult scrig rig) env sc
           ualts <- lcheckAlts fc (presence rig) (restrictEnv env rig) scrig alts
           pure (combine fc usc ualts)
  lcheck rig env (TDelayed fc r tm) = logDepth $ lcheck rig env tm
  lcheck rig env (TDelay fc r ty arg) = logDepth $ lcheck rig env arg
  lcheck rig env (TForce fc r tm) = logDepth $ lcheck rig env tm
  lcheck rig env (PrimVal fc c) = hdone fc
  lcheck rig env (PrimOp fc fn args)
     = do us <- logDepth $ traverseVect (\a => logDepth $ lcheck rig env a) args
          pure (concat fc (toList us))
  lcheck rig env (Erased _ (Dotted t)) = logDepth $ lcheck rig env t
  lcheck rig env (Erased fc _) = hdone fc
  lcheck rig env (Unmatched fc _) = hdone fc
  lcheck rig env (TType fc _) = hdone fc

  checkEnvUsage : {vars, done : _} ->
                  FC -> RigCount ->
                  Env Term vars -> HoleUsage (vars ++ done) ->
                  Term (vars ++ done) ->
                  Core ()
  checkEnvUsage fc rig [<] usage tm = pure ()
  checkEnvUsage {done} {vars = xs :< nm} fc rig (bs :< b) usage tm
      = do let pos = localPrf {later=done} {vars=xs} {n=nm}
           let used_in = count (varIdx pos) usage
           -- Adjust usage count depending on holes, as we do when
           -- checking binders
           holeFound <- if isLinear (multiplicity b)
                           then updateHoleUsage pos VarSet.empty [<] usage
                           else pure False
           let used = if isLinear (rigMult (multiplicity b) rig) &&
                         holeFound && used_in == 0
                         then 1
                         else used_in
           checkUsageOK fc used nm (rigMult (multiplicity b) rig)
           checkEnvUsage {done = [<nm] ++ done} fc rig bs
                   (rewrite appendAssociative xs [<nm] done in usage)
                   (rewrite appendAssociative xs [<nm] done in tm)

  export
  linearCheck : {vars : _} ->
                FC -> RigCount ->
                Env Term vars -> Term vars -> Core ()
  linearCheck fc rig env tm
      = do logTerm "quantity" 5 "Linearity check on " tm
           logEnv "quantity" 5 "In env" env
           used <- logDepth $ lcheck rig env tm
           log "quantity" 5 $ "Used: " ++ show used
           checkEnvUsage {done = [<]} fc rig env used tm
