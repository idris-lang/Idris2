
module Core.UnifyState

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Normalise
import Core.Options
import Core.TT
import Core.TTC
import Core.Value

import Data.List
import Libraries.Data.IntMap
import Libraries.Data.NameMap
import Libraries.Data.WithDefault

import Libraries.Data.SnocList.HasLength

%default covering

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    FC ->
                    (withLazy : Bool) ->
                    (env : Env Term vars) ->
                    (x : NF vars) -> (y : NF vars) ->
                    Constraint
     -- A resolved constraint
     Resolved : Constraint

-- a constraint on the LHS arising from checking an argument in a position
-- where we expect a polymorphic type. If, in the end, the expected type is
-- polymorphic but the argument is concrete, then the pattern match is too
-- specific
public export
data PolyConstraint : Type where
     MkPolyConstraint : {vars : _} ->
                        FC -> Env Term vars ->
                        (arg : Term vars) ->
                        (expty : NF vars) ->
                        (argty : NF vars) -> PolyConstraint

-- Explanation for why an elaborator has been delayed. It's helpful to know
-- the reason for a delay (I wish airlines and train companies knew this)
-- because it means we can choose to run only a subset (e.g. it's sometimes
-- useful to just retry the case blocks) and because we can run them in the
-- order that prioritises the best error messages.
public export
data DelayReason
      = CaseBlock
      | Ambiguity
      | RecordUpdate
      | Rewrite
      | LazyDelay

public export
Eq DelayReason where
  CaseBlock == CaseBlock = True
  Ambiguity == Ambiguity = True
  RecordUpdate == RecordUpdate = True
  Rewrite == Rewrite = True
  LazyDelay == LazyDelay = True
  _ == _ = False

public export
Ord DelayReason where
  compare x y = compare (tag x) (tag y)
    where
      -- The ordering here is chosen to give the most likely useful error
      -- messages first. For example, often the real reason for a strange error
      -- is because there's an ambiguity that can't be resolved.
      tag : DelayReason -> Int
      tag CaseBlock = 1 -- we can often proceed even if there's still some
                        -- ambiguity
      tag Ambiguity = 2
      tag LazyDelay = 3
      tag RecordUpdate = 4
      tag Rewrite = 5

public export
record UState where
  constructor MkUState
  holes : IntMap (FC, Name) -- All metavariables with no definition yet.
                            -- 'Int' is the 'Resolved' name
  guesses : IntMap (FC, Name) -- Names which will be defined when constraints solved
                              -- (also includes auto implicit searches)
  currentHoles : IntMap (FC, Name) -- Holes introduced this elaboration session
  delayedHoles : IntMap (FC, Name) -- Holes left unsolved after an elaboration,
                                   -- so we need to check again at the end whether
                                   -- they have been solved later. Doesn't include
                                   -- user defined hole names, which don't need
                                   -- to have been solved
  constraints : IntMap Constraint -- map for finding constraints by ID
  noSolve : IntMap () -- Names not to solve
                      -- If we're checking an LHS, then checking an argument can't
                      -- solve its own type, or we might end up with something
                      -- less polymorphic than it should be
  polyConstraints : List PolyConstraint -- constraints which need to be solved
                      -- successfully to check an LHS is polymorphic enough
  dotConstraints : List (Name, DotReason, Constraint) -- dot pattern constraints
  nextName : Int
  nextConstraint : Int
  delayedElab : List (DelayReason, Int, NameMap (), Core ClosedTerm)
                -- Elaborators which we need to try again later, because
                -- we didn't have enough type information to elaborate
                -- successfully yet.
                -- The 'Int' is the resolved name.
                -- NameMap () is the set of local hints at the point of delay
  logging : Bool

export
initUState : UState
initUState = MkUState
  { holes = empty
  , guesses = empty
  , currentHoles = empty
  , delayedHoles = empty
  , constraints = empty
  , noSolve = empty
  , polyConstraints = []
  , dotConstraints = []
  , nextName = 0
  , nextConstraint = 0
  , delayedElab = []
  , logging = False
  }

export
data UST : Type where

export
resetNextVar : {auto u : Ref UST UState} ->
               Core ()
resetNextVar = update UST { nextName := 0 }

-- Generate a global name based on the given root, in the current namespace
export
genName : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         n <- inCurrentNS (MN str (nextName ust))
         pure n

-- Generate a global name based on the given name, in the current namespace
export
genMVName : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Name -> Core Name
genMVName (UN str) = genName (displayUserName str)
genMVName (MN str _) = genName str
genMVName n
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         mn <- inCurrentNS (MN (show n) (nextName ust))
         pure mn

-- Generate a unique variable name based on the given root
export
genVarName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             String -> Core Name
genVarName str
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         pure (MN str (nextName ust))

-- Again, for case names
export
genCaseName : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              String -> Core Name
genCaseName root
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         inCurrentNS (CaseBlock root (nextName ust))

export
genWithName : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              String -> Core Name
genWithName root
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         inCurrentNS (WithBlock root (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              FC -> Name -> Int -> Core ()
addHoleName fc n i = update UST { holes $= insert i (fc, n),
                                  currentHoles $= insert i (fc, n) }

addGuessName : {auto u : Ref UST UState} ->
               FC -> Name -> Int -> Core ()
addGuessName fc n i = update UST { guesses $= insert i (fc, n) }

export
removeHole : {auto u : Ref UST UState} ->
             Int -> Core ()
removeHole n = update UST { holes $= delete n,
                            currentHoles $= delete n,
                            delayedHoles $= delete n }

export
removeHoleName : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Name -> Core ()
removeHoleName n
    = do defs <- get Ctxt
         whenJust (getNameID n defs.gamma) removeHole

export
addNoSolve : {auto u : Ref UST UState} ->
             Int -> Core ()
addNoSolve i = update UST { noSolve $= insert i () }

export
removeNoSolve : {auto u : Ref UST UState} ->
                Int -> Core ()
removeNoSolve i = update UST { noSolve $= delete i }

export
saveHoles : {auto u : Ref UST UState} ->
            Core (IntMap (FC, Name))
saveHoles
    = do ust <- get UST
         put UST ({ currentHoles := empty } ust)
         pure (currentHoles ust)

export
restoreHoles : {auto u : Ref UST UState} ->
               IntMap (FC, Name) -> Core ()
restoreHoles hs = update UST { currentHoles := hs }

export
removeGuess : {auto u : Ref UST UState} ->
              Int -> Core ()
removeGuess n = update UST { guesses $= delete n }

-- Get all of the hole data
export
getHoles : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getHoles = holes <$> get UST

-- Get all of the guess data
export
getGuesses : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getGuesses = guesses <$> get UST

-- Get the hole data for holes in the current elaboration session
-- (i.e. since the last 'saveHoles')
export
getCurrentHoles : {auto u : Ref UST UState} ->
                  Core (IntMap (FC, Name))
getCurrentHoles = currentHoles <$> get UST

export
isHole : {auto u : Ref UST UState} ->
         Int -> Core Bool
isHole i = isJust . lookup i <$> getHoles

export
isCurrentHole : {auto u : Ref UST UState} ->
                Int -> Core Bool
isCurrentHole i = isJust . lookup i <$> getCurrentHoles

export
setConstraint : {auto u : Ref UST UState} ->
                Int -> Constraint -> Core ()
setConstraint cid c = update UST { constraints $= insert cid c }

export
deleteConstraint : {auto u : Ref UST UState} ->
                Int -> Core ()
deleteConstraint cid = update UST { constraints $= delete cid }

export
addConstraint : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                Constraint -> Core Int
addConstraint constr
    = do ust <- get UST
         let cid = nextConstraint ust
         put UST ({ constraints $= insert cid constr,
                    nextConstraint := cid+1 } ust)
         pure cid

export
addDot : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         FC -> Env Term vars -> Name -> Term vars -> DotReason -> Term vars ->
         Core ()
addDot fc env dotarg x reason y
    = do defs <- get Ctxt
         xnf <- nf defs env x
         ynf <- nf defs env y
         update UST { dotConstraints $= ((dotarg, reason, MkConstraint fc False env xnf ynf) ::) }

export
addPolyConstraint : {vars : _} ->
                    {auto u : Ref UST UState} ->
                    FC -> Env Term vars -> Term vars -> NF vars -> NF vars ->
                    Core ()
addPolyConstraint fc env arg x@(NApp _ (NMeta _ _ _) _) y
    = update UST { polyConstraints $= ((MkPolyConstraint fc env arg x y) ::) }
addPolyConstraint fc env arg x y
    = pure ()

mkLocal : {wkns : SnocList Name} -> FC -> Binder (Term vars) -> Term (wkns <>> x :: (vars ++ done))
mkLocal fc b = Local fc (Just (isLet b)) _ (mkIsVarChiply (mkHasLength wkns))

mkConstantAppArgs : {vars : _} ->
                    Bool -> FC -> Env Term vars ->
                    (wkns : SnocList Name) ->
                    List (Term (wkns <>> (vars ++ done)))
mkConstantAppArgs lets fc [] wkns = []
mkConstantAppArgs {done} {vars = x :: xs} lets fc (b :: env) wkns
    = let rec = mkConstantAppArgs {done} lets fc env (wkns :< x) in
          if lets || not (isLet b)
             then mkLocal fc b :: rec
             else rec

mkConstantAppArgsSub : {vars : _} ->
                       Bool -> FC -> Env Term vars ->
                       Thin smaller vars ->
                       (wkns : SnocList Name) ->
                       List (Term (wkns <>> (vars ++ done)))
mkConstantAppArgsSub lets fc [] p wkns = []
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) Refl wkns
    = mkConstantAppArgs lets fc env (wkns :< x)
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) (Drop p) wkns
    = mkConstantAppArgsSub lets fc env p (wkns :< x)
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) (Keep p) wkns
    = let rec = mkConstantAppArgsSub {done} lets fc env p (wkns :< x) in
          if lets || not (isLet b)
             then mkLocal fc b :: rec
             else rec

mkConstantAppArgsOthers : {vars : _} ->
                          Bool -> FC -> Env Term vars ->
                          Thin smaller vars ->
                          (wkns : SnocList Name) ->
                          List (Term (wkns <>> (vars ++ done)))
mkConstantAppArgsOthers lets fc [] p wkns = []
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) Refl wkns
    = mkConstantAppArgsOthers lets fc env Refl (wkns :< x)
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) (Keep p) wkns
    = mkConstantAppArgsOthers lets fc env p (wkns :< x)
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) (Drop p) wkns
    = let rec = mkConstantAppArgsOthers {done} lets fc env p (wkns :< x) in
          if lets || not (isLet b)
             then mkLocal fc b :: rec
             else rec

export
applyTo : {vars : _} ->
          FC -> Term vars -> Env Term vars -> Term vars
applyTo fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} False fc env [<]) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToFull : {vars : _} ->
              FC -> Term vars -> Env Term vars -> Term vars
applyToFull fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} True fc env [<]) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToSub : {vars : _} ->
             FC -> Term vars -> Env Term vars ->
             Thin smaller vars -> Term vars
applyToSub fc tm env sub
  = let args = reverse (mkConstantAppArgsSub {done = []} True fc env sub [<]) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToOthers : {vars : _} ->
                FC -> Term vars -> Env Term vars ->
                Thin smaller vars -> Term vars
applyToOthers fc tm env sub
  = let args = reverse (mkConstantAppArgsOthers {done = []} True fc env sub [<]) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

-- Create a new metavariable with the given name and return type,
-- and return a term which is the metavariable applied to the environment
-- (and which has the given type)
-- Flag whether cycles are allowed in the result, and whether to abstract
-- over lets
export
newMetaLets : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount ->
              Env Term vars -> Name -> Term vars -> Def ->
              Bool -> Bool ->
              Core (Int, Term vars)
newMetaLets {vars} fc rig env n ty def nocyc lets
    = do let hty = if lets then abstractFullEnvType fc env ty
                           else abstractEnvType fc env ty
         let hole = { noCycles := nocyc }
                           (newDef fc n rig [] hty (specified Public) def)
         log "unify.meta" 5 $ "Adding new meta " ++ show (n, fc, rig)
         logTerm "unify.meta" 10 ("New meta type " ++ show n) hty
         idx <- addDef n hole
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} lets fc env [<]) in
                  rewrite sym (appendNilRightNeutral vars) in args

export
newMeta : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> RigCount ->
          Env Term vars -> Name -> Term vars -> Def ->
          Bool ->
          Core (Int, Term vars)
newMeta fc r env n ty def cyc = newMetaLets fc r env n ty def cyc False

mkConstant : {vars : _} ->
             FC -> Env Term vars -> Term vars -> ClosedTerm
mkConstant fc [] tm = tm
-- mkConstant {vars = x :: _} fc (Let c val ty :: env) tm
--     = mkConstant fc env (Bind fc x (Let c val ty) tm)
mkConstant {vars = x :: _} fc (b :: env) tm
    = let ty = binderType b in
          mkConstant fc env (Bind fc x (Lam fc (multiplicity b) Explicit ty) tm)

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return the replacement term (the name applied to the environment)
export
newConstant : {vars : _} ->
              {auto u : Ref UST UState} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> RigCount -> Env Term vars ->
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Int) ->
              Core (Term vars)
newConstant {vars} fc rig env tm ty constrs
    = do let def = mkConstant fc env tm
         let defty = abstractFullEnvType fc env ty
         cn <- genName "postpone"
         let guess = newDef fc cn rig [] defty (specified Public)
                            (Guess def (length env) constrs)
         log "unify.constant" 5 $ "Adding new constant " ++ show (cn, fc, rig)
         logTerm "unify.constant" 10 ("New constant type " ++ show cn) defty
         idx <- addDef cn guess
         addGuessName fc cn idx
         pure (Meta fc cn idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} True fc env [<]) in
                  rewrite sym (appendNilRightNeutral vars) in args

-- Create a new search with the given name and return type,
-- and return a term which is the name applied to the environment
-- (and which has the given type)
export
newSearch : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            FC -> RigCount -> Nat -> Name ->
            Env Term vars -> Name -> Term vars -> Core (Int, Term vars)
newSearch {vars} fc rig depth def env n ty
    = do let hty = abstractEnvType fc env ty
         let hole = newDef fc n rig [] hty (specified Public) (BySearch rig depth def)
         log "unify.search" 10 $ "Adding new search " ++ show fc ++ " " ++ show n
         logTermNF "unify.search" 10 "New search type" [] hty
         idx <- addDef n hole
         addGuessName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env [<]) in
                  rewrite sym (appendNilRightNeutral vars) in args

-- Add a hole which stands for a delayed elaborator
export
newDelayed : {vars : _} ->
             {auto u : Ref UST UState} ->
             {auto c : Ref Ctxt Defs} ->
             FC -> RigCount ->
             Env Term vars -> Name ->
             (ty : Term vars) -> Core (Int, Term vars)
newDelayed {vars} fc rig env n ty
    = do let hty = abstractEnvType fc env ty
         let hole = newDef fc n rig [] hty (specified Public) Delayed
         idx <- addDef n hole
         log "unify.delay" 10 $ "Added delayed elaborator " ++ show (n, idx)
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env [<]) in
                  rewrite sym (appendNilRightNeutral vars) in args

export
tryErrorUnify : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {default False unResolve : Bool} ->
                Core a -> Core (Either Error a)
tryErrorUnify elab
    = do ust <- get UST
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do put UST ust
                           err <- ifThenElse unResolve toFullNames pure err
                           defs' <- get Ctxt
                           put Ctxt ({ timings := timings defs' } defs)
                           pure (Left err))

export
tryUnify : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Core a -> Core a -> Core a
tryUnify elab1 elab2
    = do Right ok <- tryErrorUnify elab1
               | Left err => elab2
         pure ok

export
handleUnify : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {default False unResolve : Bool} ->
              Core a -> (Error -> Core a) -> Core a
handleUnify elab1 elab2
    = do Right ok <- tryErrorUnify {unResolve} elab1
               | Left err => elab2 err
         pure ok

-- Note that the given hole name arises from a type declaration, so needs
-- to be resolved later
export
addDelayedHoleName : {auto u : Ref UST UState} ->
                     (Int, (FC, Name)) -> Core ()
addDelayedHoleName (idx, h) = update UST { delayedHoles $= insert idx h }

export
checkDelayedHoles : {auto u : Ref UST UState} ->
                    Core (Maybe Error)
checkDelayedHoles
    = do ust <- get UST
         let hs = toList (delayedHoles ust)
         if (not (isNil hs))
            then do pure (Just (UnsolvedHoles (map snd hs)))
            else pure Nothing

-- A hole is 'valid' - i.e. okay to leave unsolved for later - as long as it's
-- not guarded by a unification problem (in which case, report that the unification
-- problem is unsolved) and it doesn't depend on an implicit pattern variable
-- (in which case, perhaps suggest binding it explicitly)
checkValidHole : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Int -> (Int, (FC, Name)) -> Core ()
checkValidHole base (idx, (fc, n))
  = when (idx >= base) $
      do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Nothing => pure ()
         case definition gdef of
              BySearch _ _ _ =>
                  do defs <- get Ctxt
                     Just ty <- lookupTyExact n (gamma defs)
                          | Nothing => pure ()
                     throw (CantSolveGoal fc (gamma defs) [] ty Nothing)
              Guess tm envb (con :: _) =>
                  do ust <- get UST
                     let Just c = lookup con (constraints ust)
                          | Nothing => pure ()
                     case c of
                          MkConstraint fc l env x y =>
                             do put UST ({ guesses := empty } ust)
                                empty <- clearDefs defs
                                xnf <- quote empty env x
                                ynf <- quote empty env y
                                throw (CantSolveEq fc (gamma defs) env xnf ynf)
                          _ => pure ()
              _ => traverse_ checkRef !(traverse getFullName
                                        ((keys (getRefs (Resolved (-1)) (type gdef)))))
  where
    checkRef : Name -> Core ()
    checkRef (PV n f)
        = throw (GenericMsg fc
                   ("Hole cannot depend on an unbound implicit " ++ show n))
    checkRef _ = pure ()

-- Bool flag says whether it's an error for there to have been holes left
-- in the last session. Usually we can leave them to the end, but it's not
-- valid for there to be holes remaining when checking a LHS.
-- Also throw an error if there are unresolved guarded constants or
-- unsolved searches
export
checkUserHolesAfter : {auto u : Ref UST UState} ->
                      {auto c : Ref Ctxt Defs} ->
                      Int -> Bool -> Core ()
checkUserHolesAfter base now
    = do gs_map <- getGuesses
         let gs = toList gs_map
         log "unify.unsolved" 10 $ "Unsolved guesses " ++ show gs
         traverse_ (checkValidHole base) gs
         hs_map <- getCurrentHoles
         let hs = toList hs_map
         let hs' = if any isUserName (map (snd . snd) hs)
                      then [] else hs
         when (now && not (isNil hs')) $
              throw (UnsolvedHoles (map snd (nubBy nameEq hs)))
         -- Note the hole names, to ensure they are resolved
         -- by the end of elaborating the current source file
         traverse_ addDelayedHoleName hs'
  where
    nameEq : (a, b, Name) -> (a, b, Name) -> Bool
    nameEq (_, _, x) (_, _, y) = x == y

export
checkUserHoles : {auto u : Ref UST UState} ->
                 {auto c : Ref Ctxt Defs} ->
                 Bool -> Core ()
checkUserHoles = checkUserHolesAfter 0

export
checkNoGuards : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                Core ()
checkNoGuards = checkUserHoles False

export
dumpHole : {auto u : Ref UST UState} ->
           {auto c : Ref Ctxt Defs} ->
           LogTopic -> Nat -> (hole : Int) -> Core ()
dumpHole s n hole
    = do ust <- get UST
         defs <- get Ctxt
         depth <- getDepth
         case !(lookupCtxtExact (Resolved hole) (gamma defs)) of
          Nothing => pure ()
          Just gdef => case (definition gdef, type gdef) of
             (Guess tm envb constraints, ty) =>
                  do logString depth s.topic n $
                       "!" ++ show !(getFullName (Resolved hole)) ++ " : "
                           ++ show !(toFullNames !(normaliseHoles defs [] ty))
                       ++ "\n\t  = "
                           ++ show !(normaliseHoles defs [] tm)
                           ++ "\n\twhen"
                     traverse_ dumpConstraint constraints
             (Hole _ p, ty) =>
                  logString depth s.topic n $
                    "?" ++ show (fullname gdef) ++ " : "
                        ++ show !(normaliseHoles defs [] ty)
                        ++ if implbind p then " (ImplBind)" else ""
                        ++ if invertible gdef then " (Invertible)" else ""
             (BySearch _ _ _, ty) =>
                  logString depth s.topic n $
                     "Search " ++ show hole ++ " : " ++
                     show !(toFullNames !(normaliseHoles defs [] ty))
             (PMDef _ args t _ _, ty) =>
                  log s 4 $
                     "Solved: " ++ show hole ++ " : " ++
                     show !(normalise defs [] ty) ++
                     " = " ++ show !(normalise defs [] (Ref emptyFC Func (Resolved hole)))
             (ImpBind, ty) =>
                  log s 4 $
                      "Bound: " ++ show hole ++ " : " ++
                      show !(normalise defs [] ty)
             (Delayed, ty) =>
                  log s 4 $
                     "Delayed elaborator : " ++
                     show !(normalise defs [] ty)
             _ => pure ()
  where
    dumpConstraint : Int -> Core ()
    dumpConstraint cid
        = do ust <- get UST
             defs <- get Ctxt
             depth <- getDepth
             case lookup cid (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => logString depth s.topic n "\tResolved"
                  Just (MkConstraint _ lazy env x y) =>
                    do logString depth s.topic n $
                         "\t  " ++ show !(toFullNames !(quote defs env x))
                                ++ " =?= " ++ show !(toFullNames !(quote defs env y))
                       empty <- clearDefs defs
                       log s 5 $
                         "\t    from " ++ show !(toFullNames !(quote empty env x))
                            ++ " =?= " ++ show !(toFullNames !(quote empty env y))
                            ++ if lazy then "\n\t(lazy allowed)" else ""

export
dumpConstraints : {auto u : Ref UST UState} ->
                  {auto c : Ref Ctxt Defs} ->
                  LogTopic -> (verbosity : Nat) -> (all : Bool) -> Core ()
dumpConstraints s n all
    = do ust <- get UST
         defs <- get Ctxt
         when !(logging s n) $ do
           let hs = toList (guesses ust) ++
                    toList (if all then holes ust else currentHoles ust)
           unless (isNil hs) $
             do depth <- getDepth
                logString depth s.topic n "--- CONSTRAINTS AND HOLES ---"
                traverse_ (dumpHole s n) (map fst hs)
