module Core.UnifyState

import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Normalise
import Core.Options
import Core.TT
import Core.TTC
import Libraries.Utils.Binary

import Libraries.Data.IntMap
import Data.List
import Libraries.Data.NameMap
import Libraries.Data.StringMap

%default covering

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    FC ->
                    (withLazy : Bool) ->
                    (blockedOn : List Name) ->
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) ->
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : {vars : _} ->
                       FC ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

export
TTC Constraint where
  toBuf b (MkConstraint {vars} fc l block env x y)
     = do tag 0; toBuf b vars; toBuf b l
          toBuf b block
          toBuf b fc; toBuf b env; toBuf b x; toBuf b y
  toBuf b (MkSeqConstraint {vars} fc env xs ys)
     = do tag 1; toBuf b vars; toBuf b fc; toBuf b env; toBuf b xs; toBuf b ys
  toBuf b Resolved = tag 2

  fromBuf b
      = case !getTag of
             0 => do vars <- fromBuf b
                     fc <- fromBuf b; l <- fromBuf b
                     block <- fromBuf b
                     env <- fromBuf b
                     x <- fromBuf b; y <- fromBuf b
                     pure (MkConstraint {vars} fc l block env x y)
             1 => do vars <- fromBuf b
                     fc <- fromBuf b; env <- fromBuf b
                     xs <- fromBuf b; ys <- fromBuf b
                     pure (MkSeqConstraint {vars} fc env xs ys)
             2 => pure Resolved
             _ => corrupt "Constraint"

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
  dotConstraints : List (Name, DotReason, Constraint) -- dot pattern constraints
  nextName : Int
  nextConstraint : Int
  delayedElab : List (Nat, Int, NameMap (), Core ClosedTerm)
                -- Elaborators which we need to try again later, because
                -- we didn't have enough type information to elaborate
                -- successfully yet.
                -- 'Nat' is the priority (lowest first)
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
resetNextVar
    = do ust <- get UST
         put UST (record { nextName = 0 } ust)

-- Generate a global name based on the given root, in the current namespace
export
genName : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         n <- inCurrentNS (MN str (nextName ust))
         pure n

-- Generate a global name based on the given name, in the current namespace
export
genMVName : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Name -> Core Name
genMVName (UN str) = genName str
genMVName (MN str _) = genName str
genMVName (RF str) = genName str
genMVName n
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         mn <- inCurrentNS (MN (show n) (nextName ust))
         pure mn

-- Generate a unique variable name based on the given root
export
genVarName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             String -> Core Name
genVarName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (MN str (nextName ust))

-- Again, for case names
export
genCaseName : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              String -> Core Name
genCaseName root
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         inCurrentNS (CaseBlock root (nextName ust))

export
genWithName : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              String -> Core Name
genWithName root
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         inCurrentNS (WithBlock root (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              FC -> Name -> Int -> Core ()
addHoleName fc n i
    = do ust <- get UST
         put UST (record { holes $= insert i (fc, n),
                           currentHoles $= insert i (fc, n) } ust)

addGuessName : {auto u : Ref UST UState} ->
               FC -> Name -> Int -> Core ()
addGuessName fc n i
    = do ust <- get UST
         put UST (record { guesses $= insert i (fc, n)  } ust)

export
removeHole : {auto u : Ref UST UState} ->
             Int -> Core ()
removeHole n
    = do ust <- get UST
         put UST (record { holes $= delete n,
                           currentHoles $= delete n,
                           delayedHoles $= delete n } ust)

export
removeHoleName : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Name -> Core ()
removeHoleName n
    = do defs <- get Ctxt
         let Just i = getNameID n (gamma defs)
             | Nothing => pure ()
         removeHole i

export
saveHoles : {auto u : Ref UST UState} ->
            Core (IntMap (FC, Name))
saveHoles
    = do ust <- get UST
         put UST (record { currentHoles = empty } ust)
         pure (currentHoles ust)

export
restoreHoles : {auto u : Ref UST UState} ->
               IntMap (FC, Name) -> Core ()
restoreHoles hs
    = do ust <- get UST
         put UST (record { currentHoles = hs } ust)

export
removeGuess : {auto u : Ref UST UState} ->
              Int -> Core ()
removeGuess n
    = do ust <- get UST
         put UST (record { guesses $= delete n } ust)

-- Get all of the hole data
export
getHoles : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getHoles
    = do ust <- get UST
         pure (holes ust)

-- Get all of the guess data
export
getGuesses : {auto u : Ref UST UState} ->
           Core (IntMap (FC, Name))
getGuesses
    = do ust <- get UST
         pure (guesses ust)

-- Get the hole data for holes in the current elaboration session
-- (i.e. since the last 'saveHoles')
export
getCurrentHoles : {auto u : Ref UST UState} ->
                  Core (IntMap (FC, Name))
getCurrentHoles
    = do ust <- get UST
         pure (currentHoles ust)

export
isHole : {auto u : Ref UST UState} ->
         Int -> Core Bool
isHole i
    = do ust <- get UST
         pure (maybe False (const True) (lookup i (holes ust)))

export
isCurrentHole : {auto u : Ref UST UState} ->
                Int -> Core Bool
isCurrentHole i
    = do ust <- get UST
         pure (maybe False (const True) (lookup i (currentHoles ust)))

export
setConstraint : {auto u : Ref UST UState} ->
                Int -> Constraint -> Core ()
setConstraint cid c
    = do ust <- get UST
         put UST (record { constraints $= insert cid c } ust)

export
deleteConstraint : {auto u : Ref UST UState} ->
                Int -> Core ()
deleteConstraint cid
    = do ust <- get UST
         put UST (record { constraints $= delete cid } ust)

export
addConstraint : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                Constraint -> Core Int
addConstraint constr
    = do ust <- get UST
         let cid = nextConstraint ust
         put UST (record { constraints $= insert cid constr,
                           nextConstraint = cid+1 } ust)
         pure cid

export
addDot : {vars : _} ->
         {auto u : Ref UST UState} ->
         FC -> Env Term vars -> Name -> Term vars -> DotReason -> Term vars ->
         Core ()
addDot fc env dotarg x reason y
    = do ust <- get UST
         put UST (record { dotConstraints $=
                             ((dotarg, reason, MkConstraint fc False [] env x y) ::)
                         } ust)

mkConstantAppArgs : {vars : _} ->
                    Bool -> FC -> Env Term vars ->
                    (wkns : List Name) ->
                    List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgs lets fc [] wkns = []
mkConstantAppArgs {done} {vars = x :: xs} lets fc (b :: env) wkns
    = let rec = mkConstantAppArgs {done} lets fc env (wkns ++ [x]) in
          if lets || not (isLet b)
             then Local fc (Just (isLet b)) (length wkns) (mkVar wkns) ::
                  rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
             else rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
  where
    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)

mkConstantAppArgsSub : {vars : _} ->
                       Bool -> FC -> Env Term vars ->
                       SubVars smaller vars ->
                       (wkns : List Name) ->
                       List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgsSub lets fc [] p wkns = []
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) SubRefl wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgs lets fc env (wkns ++ [x])
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) (DropCons p) wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgsSub lets fc env p (wkns ++ [x])
mkConstantAppArgsSub {done} {vars = x :: xs}
                        lets fc (b :: env) (KeepCons p) wkns
    = let rec = mkConstantAppArgsSub {done} lets fc env p (wkns ++ [x]) in
          if lets || not (isLet b)
             then Local fc (Just (isLet b)) (length wkns) (mkVar wkns) ::
                  rewrite appendAssociative wkns [x] (xs ++ done) in rec
             else rewrite appendAssociative wkns [x] (xs ++ done) in rec
  where
    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)

mkConstantAppArgsOthers : {vars : _} ->
                          Bool -> FC -> Env Term vars ->
                          SubVars smaller vars ->
                          (wkns : List Name) ->
                          List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgsOthers lets fc [] p wkns = []
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) SubRefl wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgsOthers lets fc env SubRefl (wkns ++ [x])
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) (KeepCons p) wkns
    = rewrite appendAssociative wkns [x] (xs ++ done) in
              mkConstantAppArgsOthers lets fc env p (wkns ++ [x])
mkConstantAppArgsOthers {done} {vars = x :: xs}
                        lets fc (b :: env) (DropCons p) wkns
    = let rec = mkConstantAppArgsOthers {done} lets fc env p (wkns ++ [x]) in
          if lets || not (isLet b)
             then Local fc (Just (isLet b)) (length wkns) (mkVar wkns) ::
                  rewrite appendAssociative wkns [x] (xs ++ done) in rec
             else rewrite appendAssociative wkns [x] (xs ++ done) in rec
  where
    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)


export
applyTo : {vars : _} ->
          FC -> Term vars -> Env Term vars -> Term vars
applyTo fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToFull : {vars : _} ->
              FC -> Term vars -> Env Term vars -> Term vars
applyToFull fc tm env
  = let args = reverse (mkConstantAppArgs {done = []} True fc env []) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToSub : {vars : _} ->
             FC -> Term vars -> Env Term vars ->
             SubVars smaller vars -> Term vars
applyToSub fc tm env sub
  = let args = reverse (mkConstantAppArgsSub {done = []} True fc env sub []) in
        apply fc tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToOthers : {vars : _} ->
                FC -> Term vars -> Env Term vars ->
                SubVars smaller vars -> Term vars
applyToOthers fc tm env sub
  = let args = reverse (mkConstantAppArgsOthers {done = []} True fc env sub []) in
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
         let hole = record { noCycles = nocyc }
                           (newDef fc n rig [] hty Public def)
         log "unify.meta" 5 $ "Adding new meta " ++ show (n, fc, rig)
         logTerm "unify.meta" 10 ("New meta type " ++ show n) hty
         defs <- get Ctxt
         idx <- addDef n hole
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} lets fc env []) in
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
         let guess = newDef fc cn rig [] defty Public
                            (Guess def (length env) constrs)
         log "unify.constant" 5 $ "Adding new constant " ++ show (cn, fc, rig)
         logTerm "unify.constant" 10 ("New constant type " ++ show cn) defty
         idx <- addDef cn guess
         addGuessName fc cn idx
         pure (Meta fc cn idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} True fc env []) in
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
         let hole = newDef fc n rig [] hty Public (BySearch rig depth def)
         log "unify.search" 10 $ "Adding new search " ++ show fc ++ " " ++ show n
         logTermNF "unify.search" 10 "New search type" [] hty
         idx <- addDef n hole
         addGuessName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
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
         let hole = newDef fc n rig [] hty Public Delayed
         idx <- addDef n hole
         log "unify.delay" 10 $ "Added delayed elaborator " ++ show (n, idx)
         addHoleName fc n idx
         pure (idx, Meta fc n idx envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} False fc env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

export
tryErrorUnify : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                Core a -> Core (Either Error a)
tryErrorUnify elab
    = do ust <- get UST
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do put UST ust
                           defs' <- get Ctxt
                           put Ctxt (record { timings = timings defs' } defs)
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
              Core a -> (Error -> Core a) -> Core a
handleUnify elab1 elab2
    = do Right ok <- tryErrorUnify elab1
               | Left err => elab2 err
         pure ok

-- Note that the given hole name arises from a type declaration, so needs
-- to be resolved later
export
addDelayedHoleName : {auto u : Ref UST UState} ->
                     (Int, (FC, Name)) -> Core ()
addDelayedHoleName (idx, h)
    = do ust <- get UST
         put UST (record { delayedHoles $= insert idx h } ust)

export
checkDelayedHoles : {auto u : Ref UST UState} ->
                    {auto c : Ref Ctxt Defs} ->
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
         ust <- get UST
         Just gdef <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Nothing => pure ()
         case definition gdef of
              BySearch _ _ _ =>
                  do defs <- get Ctxt
                     Just ty <- lookupTyExact n (gamma defs)
                          | Nothing => pure ()
                     throw (CantSolveGoal fc [] ty)
              Guess tm envb (con :: _) =>
                  do ust <- get UST
                     let Just c = lookup con (constraints ust)
                          | Nothing => pure ()
                     case c of
                          MkConstraint fc l blocked env x y =>
                             do put UST (record { guesses = empty } ust)
                                xnf <- normaliseHoles defs env x
                                ynf <- normaliseHoles defs env y
                                throw (CantSolveEq fc env xnf ynf)
                          MkSeqConstraint fc env (x :: _) (y :: _) =>
                             do put UST (record { guesses = empty } ust)
                                xnf <- normaliseHoles defs env x
                                ynf <- normaliseHoles defs env y
                                throw (CantSolveEq fc env xnf ynf)
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
dumpHole' : {auto u : Ref UST UState} ->
            {auto c : Ref Ctxt Defs} ->
            LogLevel -> (hole : Int) -> Core ()
dumpHole' lvl hole
    = do ust <- get UST
         defs <- get Ctxt
         when (keepLog lvl (logLevel $ session $ options defs)) $ do
               defs <- get Ctxt
               case !(lookupCtxtExact (Resolved hole) (gamma defs)) of
                 Nothing => pure ()
                 Just gdef => case (definition gdef, type gdef) of
                    (Guess tm envb constraints, ty) =>
                         do log' lvl $ "!" ++ show !(getFullName (Resolved hole)) ++ " : " ++
                                              show !(toFullNames !(normaliseHoles defs [] ty))
                            log' lvl $ "\t  = " ++ show !(normaliseHoles defs [] tm)
                                            ++ "\n\twhen"
                            traverse_ dumpConstraint constraints
                    (Hole _ p, ty) =>
                         log' lvl $ "?" ++ show (fullname gdef) ++ " : " ++
                                           show !(normaliseHoles defs [] ty)
                                           ++ if implbind p then " (ImplBind)" else ""
                                           ++ if invertible gdef then " (Invertible)" else ""
                    (BySearch _ _ _, ty) =>
                         log' lvl $ "Search " ++ show hole ++ " : " ++
                                           show !(toFullNames !(normaliseHoles defs [] ty))
                    (PMDef _ args t _ _, ty) =>
                         log' (withVerbosity 4 lvl) $
                            "Solved: " ++ show hole ++ " : " ++
                            show !(normalise defs [] ty) ++
                            " = " ++ show !(normalise defs [] (Ref emptyFC Func (Resolved hole)))
                    (ImpBind, ty) =>
                         log' (withVerbosity 4 lvl) $
                             "Bound: " ++ show hole ++ " : " ++
                             show !(normalise defs [] ty)
                    (Delayed, ty) =>
                         log' (withVerbosity 4 lvl) $
                            "Delayed elaborator : " ++
                            show !(normalise defs [] ty)
                    _ => pure ()
  where
    dumpConstraint : Int -> Core ()
    dumpConstraint n
        = do ust <- get UST
             defs <- get Ctxt
             case lookup n (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => log' lvl "\tResolved"
                  Just (MkConstraint _ lazy _ env x y) =>
                    do log' lvl $ "\t  " ++ show !(toFullNames !(normalise defs env x))
                                       ++ " =?= " ++ show !(toFullNames !(normalise defs env y))
                       log' (withVerbosity 5 lvl)
                                $ "\t    from " ++ show !(toFullNames x)
                                      ++ " =?= " ++ show !(toFullNames y) ++
                               if lazy then "\n\t(lazy allowed)" else ""
                  Just (MkSeqConstraint _ _ xs ys) =>
                       log' lvl $ "\t\t" ++ show xs ++ " =?= " ++ show ys

export
dumpConstraints : {auto u : Ref UST UState} ->
                  {auto c : Ref Ctxt Defs} ->
                  (topics : String) -> (verbosity : Nat) ->
                  (all : Bool) ->
                  Core ()
dumpConstraints str n all
    = do ust <- get UST
         defs <- get Ctxt
         let lvl = mkLogLevel str n
         when (keepLog lvl (logLevel $ session $ options defs)) $
            do let hs = toList (guesses ust) ++
                        toList (if all then holes ust else currentHoles ust)
               case hs of
                    [] => pure ()
                    _ => do log' lvl "--- CONSTRAINTS AND HOLES ---"
                            traverse_ (dumpHole' lvl) (map fst hs)
