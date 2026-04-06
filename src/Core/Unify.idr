module Core.Unify

import Core.Context.Log
import Core.Env
import Core.Options
import Core.TT.Binder
import public Core.UnifyState

import Data.Maybe
import Data.Vect

import Core.Evaluate.Value
import Core.Evaluate.Quote
import Core.Evaluate.Normalise
import Core.Evaluate.Convert
import Core.Evaluate.Expand
import Core.Evaluate
import Data.SnocList
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.VarSet
import Libraries.Data.IntMap
import Libraries.Data.NameMap
import Libraries.Data.NatSet

%default covering

public export
data UnifyMode = InLHS
               | InTerm
               | InMatch
               | InSearch

-- Need to record if we're at the top level or not, because top level things
-- can have Force and Delay inserted, and may have been postponed.
public export
record UnifyInfo where
  constructor MkUnifyInfo
  atTop : Bool
  umode : UnifyMode

export
inTerm : UnifyInfo
inTerm = MkUnifyInfo True InTerm

export
inLHS : UnifyInfo
inLHS = MkUnifyInfo True InLHS

export
inMatch : UnifyInfo
inMatch = MkUnifyInfo True InMatch

export
inSearch : UnifyInfo
inSearch = MkUnifyInfo True InSearch

lower : UnifyInfo -> UnifyInfo
lower = { atTop := False }

Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InMatch == InMatch = True
   InSearch == InSearch = True
   _ == _ = False

Eq UnifyInfo where
  x == y = atTop x == atTop y && umode x == umode y

Show UnifyMode where
  show InLHS = "InLHS"
  show InTerm = "InTerm"
  show InMatch = "InMatch"
  show InSearch = "InSearch"

Show UnifyInfo where
  show (MkUnifyInfo t u) = "{UnifyInfo atTop=\{show t} umode=\{show u}}"

-- If we're unifying a Lazy type with a non-lazy type, we need to add an
-- explicit force or delay to the first argument to unification. This says
-- which to add, if any. Can only added at the very top level.
public export
data AddLazy = NoLazy | AddForce LazyReason | AddDelay LazyReason

export
Show AddLazy where
  show NoLazy = "NoLazy"
  show (AddForce _) = "AddForce"
  show (AddDelay _) = "AddDelay"

public export
record UnifyResult where
  constructor MkUnifyResult
  constraints : List Int
  holesSolved : Bool -- did we solve any holes
  namesSolved : List Int -- which ones did we solve (as name indices)
  addLazy : AddLazy

export
Show UnifyResult where
  show a = "constraints: " ++ show a.constraints
    ++ ", holesSolved: " ++ show a.holesSolved
    ++ ", namesSolved: " ++ show a.namesSolved
    ++ ", addLazy: " ++ show a.addLazy

union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)
                            (namesSolved u1 ++ namesSolved u2)
                            NoLazy -- only top level, so assume no annotation

unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False [] NoLazy
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False [] NoLazy

success : UnifyResult
success = MkUnifyResult [] False [] NoLazy

solvedHole : Int -> UnifyResult
solvedHole n = MkUnifyResult [] True [n] NoLazy

public export
interface Unify tm where
  -- Unify returns a list of ids referring to newly added constraints
  unifyD : {vars : Scope} ->
           Ref Ctxt Defs ->
           Ref UST UState ->
           UnifyInfo ->
           FC -> Env Term vars ->
           tm vars -> tm vars ->
           Core UnifyResult
  -- As unify but at the top level can allow lazy/non-lazy to be mixed in
  -- order to infer annotations
  unifyWithLazyD : {vars : _} ->
                   Ref Ctxt Defs ->
                   Ref UST UState ->
                   UnifyInfo ->
                   FC -> Env Term vars ->
                   tm vars -> tm vars ->
                   Core UnifyResult
  unifyWithLazyD = unifyD

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}
  -- Defined in Core.AutoSearch
  export
  search : {vars : _} ->
           FC -> RigCount ->
           (defaults : Bool) -> (depth : Nat) ->
           (defining : Name) -> (topTy : Term vars) -> Env Term vars ->
           Core (Term vars)

  -- TODO: Should we prefer interface here?
  -- Blindly copied from Yaffle
  namespace Value
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value f vars -> Value f' vars -> Core UnifyResult

    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value f vars -> Value f' vars -> Core UnifyResult

  namespace Term
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult

ufail : FC -> String -> Core a
ufail loc msg = throw (GenericMsg loc msg)

convertError : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               FC -> Env Term vars -> Value f vars -> Value f' vars -> Core a
convertError loc env x y
    = do defs <- get Ctxt
         throw (CantConvert loc (gamma defs) env !(quote env x) !(quote env y))

convertGluedError : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    FC -> Env Term vars -> Glued vars -> Glued vars -> Core a
convertGluedError loc env x y
    = do defs <- get Ctxt
         throw (CantConvert loc (gamma defs) env !(quote env x) !(quote env y))

convertErrorS : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Bool -> FC -> Env Term vars -> Value f vars -> Value f' vars -> Core a
convertErrorS s loc env x y
    = if s then convertError loc env y x
           else convertError loc env x y

-- Find all the metavariables required by each of the given names.
-- We'll assume all meta solutions are of the form STerm exp.
chaseMetas : {auto c : Ref Ctxt Defs} ->
             List Name -> NameMap () -> Core (List Name)
chaseMetas [] all = pure (keys all)
chaseMetas (n :: ns) all
    = case lookup n all of
           Just _ => chaseMetas ns all
           _ => do defs <- get Ctxt
                   Just (Function _ soln _ _) <- lookupDefExact n (gamma defs)
                        | _ => chaseMetas ns (insert n () all)
                   let sns = keys (getMetas soln)
                   chaseMetas (sns ++ ns) (insert n () all)

-- Get all the metavariable names used by the term (recursively, so we
-- can do the occurs check)
getMetaNames : {auto c : Ref Ctxt Defs} ->
               Term vars -> Core (List Name)
getMetaNames tm
    = let metas = getMetas tm in
          chaseMetas (keys metas) empty

postpone : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> UnifyInfo -> String ->
           Env Term vars -> Value f vars -> Value f' vars -> Core UnifyResult
postpone loc mode logstr env x y
    = do log "unify.postpone" 10 $ "Begin postponing \"\{logstr}\""
         defs <- get Ctxt
         xtm <- quote env x
         ytm <- quote env y
         logC "unify.postpone" 10 $
              do xf <- toFullNames xtm
                 yf <- toFullNames ytm
                 pure (logstr ++ ": " ++ show xf ++ " =?= " ++ show yf)

         -- If we're blocked because a name is undefined, give up
         checkDefined defs x
         checkDefined defs y

         c <- addConstraint (MkConstraint loc (atTop mode) env xtm ytm)
         log "unify.postpone" 10 $
                 show c ++ " NEW CONSTRAINT " ++ show loc
         logTerm "unify.postpone" 10 "X" xtm
         logTerm "unify.postpone" 10 "Y" ytm
         pure (constrain c)
  where
    checkDefined : forall f . Defs -> Value f vars -> Core ()
    checkDefined defs (VApp _ _ n _ _)
        = do Just _ <- lookupCtxtExact n (gamma defs)
                  | _ => undefinedName loc n
             pure ()
    checkDefined _ _ = pure ()

    undefinedN : Name -> Core Bool
    undefinedN n
        = do defs <- get Ctxt
             pure $ case !(lookupDefExact n (gamma defs)) of
                  Just (Hole {}) => True
                  Just (BySearch {}) => True
                  Just (Guess {}) => True
                  _ => False

postponeS : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Bool -> FC -> UnifyInfo -> String -> Env Term vars ->
            Value f vars -> Value f' vars ->
            Core UnifyResult
postponeS s loc mode logstr env x y
    = if s then postpone loc (lower mode) logstr env y x
           else postpone loc mode logstr env x y

unifyArgs : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            UnifyInfo -> FC -> Env Term vars ->
            List (Core (Glued vars)) -> List (Core (Glued vars)) ->
            Core UnifyResult
unifyArgs mode loc env [] [] = pure success
unifyArgs mode loc env (cx :: cxs) (cy :: cys)
    = do -- Do later arguments first, since they may depend on earlier
         -- arguments and use their solutions.
         cs <- logDepth $ unifyArgs mode loc env cxs cys
         -- We might know more about cx and cy now, so normalise again to
         -- reduce any newly solved holes
         logC "unify" 20 $ pure $ "unifyArgs done: " ++ show cs

         cx' <- nf env !(quote env !cx)
         logNF "unify.application" 20 "unifyArgs cx'" env cx'
         cy' <- nf env !(quote env !cy)
         logNF "unify.application" 20 "unifyArgs cy'" env cy'

         res <- unify (lower mode) loc env cx' cy'
         log "unify.application" 20 "unifyArgs res \{show res}"

         pure (union res cs)
unifyArgs mode loc env _ _ = ufail loc ""

unifySpine : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyInfo -> FC -> Env Term vars ->
             Spine vars -> Spine vars ->
             Core UnifyResult
unifySpine mode fc env [<] [<] = pure success
unifySpine mode fc env (cxs :< ex) (cys :< ey)
    = do -- We might know more about cx and cy now, so normalise again to
         -- reduce any newly solved holes
         cx' <- logQuiet $ do nf env !(quote env !(value ex))
         logNF "unify.application" 20 "unifySpine cx'" env cx'

         cy' <- logQuiet $ do nf env !(quote env !(value ey))
         logNF "unify.application" 20 "unifySpine cy'" env cy'

         res <- unify (lower mode) fc env cx' cy'
         log "unify.application" 20 "unifySpine res \{show res}"

         cs <- logDepth $ unifySpine mode fc env cxs cys
         logC "unify" 20 $ pure $ "unifySpine done: " ++ show cs
         pure (union cs res)
unifySpine mode fc env _ _ = ufail fc ""

unifySpineMetaArg : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyInfo -> FC -> Env Term vars ->
             Spine vars -> Spine vars ->
             Core UnifyResult
unifySpineMetaArg mode fc env [<] [<] = pure success
unifySpineMetaArg mode fc env (cxs :< ex) (cys :< ey)
    = do -- We might know more about cx and cy now, so normalise again to
         -- reduce any newly solved holes
         cx' <- value ex
         logC "unify.application" 50 $ pure "unifySpine cx Glue Spine \{show cx'}"
         cx' <- quote env cx'
         logC "unify.application" 50 $ pure "unifySpine cx Term \{show cx'}"
         cx' <- nf env cx'
         logC "unify.application" 50 $ pure "unifySpine cx Glue NF \{show cx'}"

         logNF "unify.application" 20 "unifySpine cx'" env cx'

         cy' <- value ey
         logC "unify.application" 50 $ pure "unifySpine cy Glue Spine \{show cy'}"
         cy' <- quote env cy'
         logC "unify.application" 50 $ pure "unifySpine cy Term \{show cy'}"
         cy' <- nf env cy'
         logC "unify.application" 50 $ pure "unifySpine cy Glue NF \{show cy'}"

         logNF "unify.application" 20 "unifySpine cy'" env cy'

         res <- unifySpineEntry (lower mode) cx' cy'
         log "unify.application" 20 "unifySpine res \{show res}"

         cs <- logDepth $ unifySpineMetaArg mode fc env cxs cys
         pure (union cs res)
    where
      unifySpineEntry : UnifyInfo -> Glued vars -> Glued vars -> Core UnifyResult
      unifySpineEntry mode xnf ynf
          = do defs <- get Ctxt
               empty <- clearDefs defs
               -- If one's a meta and the other isn't, don't reduce at all
               case (xnf, ynf) of
                     (VMeta {}, VMeta {})
                         => unify mode fc env xnf ynf
                     (VMeta {}, _)
                         => do ytm <- logQuiet $ quote env ynf
                               put Ctxt empty
                               ynf' <- nf env ytm
                               put Ctxt defs
                               logC "unify" 20 $
                                 do xtm <- logQuiet $ quote env xnf
                                    pure $ "Don't reduce at all (left): " ++ show xtm ++ " and " ++ show ytm
                               cs <- unify mode fc env xnf ynf'
                               case constraints cs of
                                   [] => pure cs
                                   _  => unify mode fc env xnf ynf
                     (_, VMeta {})
                         => do xtm <- logQuiet $ quote env xnf
                               put Ctxt empty
                               xnf' <- nf env xtm
                               put Ctxt defs
                               logC "unify" 20 $
                                 do ytm <- logQuiet $ quote env ynf
                                    pure $ "Don't reduce at all (right): " ++ show {ty=Term _} ytm ++ " and " ++ show xtm
                               cs <- unify mode fc env xnf' ynf
                               case constraints cs of
                                   [] => pure cs
                                   _  => do unify mode fc env xnf ynf
                     _ => unify mode fc env xnf ynf
unifySpineMetaArg mode fc env _ _ = ufail fc ""

convertSpine : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Env Term vars ->
               Spine vars -> Spine vars ->
               Core Bool
convertSpine fc env [<] [<] = pure True
convertSpine fc env (cxs :< ex) (cys :< ey)
    = do cx' <- logQuiet $ value ex
         cy' <- logQuiet $ value ey
         logNF "unify.application" 20 "convertSpine cx'" env cx'
         logNF "unify.application" 20 "convertSpine cy'" env cy'

         res <- convert env cx' cy'
         log "unify.application" 20 "convertSpine res \{show res}"

         if res
           then logDepth $ convertSpine fc env cxs cys
           else pure False
convertSpine fc env _ _ = pure False

-- Get the variables in an application argument list; fail if any arguments
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
-- We return a list (because the order matters) and a set (for easy
-- querying)
getVars : SnocList (NF vars) -> Maybe (SnocList (Var vars), VarSet vars)
getVars = go [<] VarSet.empty where

  go : SnocList (Var vars) -> VarSet vars ->
       SnocList (NF vars) -> Maybe (SnocList (Var vars), VarSet vars)
  go acc got [<] = Just (acc, got)
  go acc got (xs :< VErased fc (Dotted t)) = go acc got (xs :< t)
  go acc got (xs :< VLocal fc idx p [<])
    = let v := MkVar p in
      if v `VarSet.elem` got then Nothing
         else go (acc :< v) (VarSet.insert v got) xs
  go acc got (xs :< VAs _ _ _ p) = go acc got (xs :< p)
  go acc _ (xs :< _) = Nothing

-- Update the variable list to point into the sub environment
-- (All of these will succeed because the Thin we have comes from
-- the list of variable uses! It's not stated in the type, though.)
updateVars : SnocList (Var {a = Name} vars) -> Thin newvars vars -> SnocList (Var newvars)
updateVars [<] svs = [<]
updateVars (ps :< p) svs
    = case shrink p svs of
            Nothing => updateVars ps svs
            Just p' => updateVars ps svs :< p'

{- Applying the pattern unification rule is okay if:
   * Arguments are all distinct local variables
   * The metavariable name doesn't appear in the unifying term
   * The local variables which appear in the term are all arguments to
     the metavariable application (not checked here, checked with the
     result of `patternEnv`)

   Return the subset of the environment used in the arguments
   to which the metavariable is applied. If this environment is enough
   to check the term we're unifying with, and that term doesn't use the
   metavariable name, we can safely apply the rule.

   Also, return the list of arguments the metavariable was applied to, to
   make sure we use them in the right order when we build the solution.
-}
patternEnv : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             Env Term vars -> SnocList (Glued vars) ->
             Core (Maybe (newvars ** (SnocList (Var newvars),
                                     Thin newvars vars)))
patternEnv {vars} env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         -- [Note] Restore logging sequence
         args' <- traverseSnocList expand args
         pure $
           case getVars args' of
             Nothing => Nothing
             Just (vslist, vsset) =>
               let (newvars ** svs) = fromVarSet _ vsset in
                 Just (newvars ** (updateVars (reverse vslist) svs, svs))

getVarsTm : SnocList (Term vars) -> Maybe (SnocList (Var vars), VarSet vars)
getVarsTm = go [<] VarSet.empty where

  go : SnocList (Var vars) -> VarSet vars ->
       SnocList (Term vars) -> Maybe (SnocList (Var vars), VarSet vars)
  go acc got [<] = Just (acc, got)
  go acc got (xs :< Local fc r idx p)
    = let v := MkVar p in
      if v `VarSet.elem` got then Nothing
         else go (acc :< v) (VarSet.insert v got) xs
  go acc _ (xs :< _) = Nothing

export
patternEnvTm : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               Env Term vars -> SnocList (Term vars) ->
               Core (Maybe (newvars ** (SnocList (Var newvars),
                                       Thin newvars vars)))
patternEnvTm {vars} env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         pure $ case getVarsTm args of
           Nothing => Nothing
           Just (vslist, vsset) =>
             let (newvars ** svs) = fromVarSet _ vsset in
                 Just (newvars ** (updateVars (reverse vslist) svs, svs))

-- Check that the metavariable name doesn't occur in the solution.
-- If it does, normalising might help. If it still does, that's an error.
occursCheck : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> Env Term vars -> UnifyInfo ->
              Name -> Term vars -> Core (Maybe (Term vars))
occursCheck fc env mode mname tm
    = do solmetas <- getMetaNames tm
         let False = mname `elem` solmetas
             | _ => do defs <- get Ctxt
                       tmnf <- normalise env tm
                       solmetas <- getMetaNames tmnf
                       if mname `elem` solmetas
                          then do failOnStrongRigid False
                                     (throw (CyclicMeta fc env mname tmnf))
                                     tmnf
                                  pure Nothing
                          else pure $ Just tmnf
         pure $ Just tm
  where
    -- Throw an occurs check failure if the name appears 'strong rigid',
    -- that is, under a constructor form rather than a function, in the
    -- term
    failOnStrongRigid : Bool -> Core () -> Term vars -> Core ()
    failOnStrongRigid bad err (Meta _ n _ _)
        = if bad && n == mname
             then err
             else pure ()
    failOnStrongRigid bad err tm
        = case getFnArgs tm of
               (f, []) => pure ()
               (Ref _ Func _, _) => pure () -- might reduce away, just block
               (Ref _ _ _, args) => traverse_ (failOnStrongRigid True err) args
               (f, args) => traverse_ (failOnStrongRigid bad err) args

-- How the variables in a metavariable definition map to the variables in
-- the solution term (the Var newvars)
--
-- TODO factor out as a renaming
-- TODO use `All` "quantifier"
data IVars : Scope -> Scoped where
     INil : IVars Scope.empty newvars
     ICons : Maybe (Var newvars) -> IVars vs newvars ->
             IVars (Scope.bind vs v) newvars

Weaken (IVars vs) where
  weakenNs s INil = INil
  weakenNs s (ICons t ts) = ICons (weakenNs @{MaybeWeaken} s t) (weakenNs s ts)

getIVars : IVars vs ns -> List (Maybe (Var ns))
getIVars INil = []
getIVars (ICons v vs) = v :: getIVars vs

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and returning the term
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
tryInstantiate : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars, newvars : _} ->
              FC -> UnifyInfo -> Env Term vars ->
              (metavar : Name) -> (mref : Int) -> (numargs : Nat) ->
              (mdef : GlobalDef) ->
              List (Var newvars) -> -- Variable each argument maps to
              Term vars -> -- original, just for error message
              Term newvars -> -- shrunk environment
              Core Bool -- postpone if the type is yet unknown
tryInstantiate {newvars} loc mode env mname mref num mdef locs otm tm
    = do logTerm "unify.instantiate" 5 ("Instantiating in " ++ show !(traverse toFullNames (asList newvars))) !(toFullNames tm)
--          let Hole _ _ = definition mdef
--              | def => ufail {a=()} loc (show mname ++ " already resolved as " ++ show def)
         case fullname mdef of
              PV pv pi => throw (PatternVariableUnifies loc (getLoc otm) env (PV pv pi) otm)
              _ => pure ()
         defs <- get Ctxt
         tynf <- nf Env.empty (type mdef)
         logNF "unify.instantiate" 5 "tynf" Env.empty tynf
         ty <- quoteBinders Env.empty tynf
                     -- make sure we have all the pi binders we need in the
                     -- type to make the metavariable definition
         logTerm "unify.instantiate" 5 ("Type: " ++ show !(toFullNames mname)) (type mdef)
         logTerm "unify.instantiate" 5 ("Type: " ++ show mname) ty
         log "unify.instantiate" 5 ("With locs: " ++ show locs)
         log "unify.instantiate" 5 ("From vars: " ++ show (asList newvars))

         defs <- get Ctxt
         -- Try to instantiate the hole
         Just rhs <- mkDef locs INil tm ty
           | _ => do
               log "unify.instantiate" 5 "Postponed"
               pure False

         logTerm "unify.instantiate" 5 "Definition" rhs
         let simpleDef = MkPMDefInfo (SolvedHole num)
                                     (not (isUserName mname) && isSimple rhs)
                                     False
         let newdef = { definition := Function simpleDef rhs rhs Nothing } mdef
         ignore $ addDef (Resolved mref) newdef
         removeHole mref
         pure True
  where
    precise : Bool
    precise
        = case definition mdef of
               Hole _ p => precisetype p
               _ => False

    -- A solution is deemed simple enough to inline if either:
    --   * It is smaller than some threshold and has no metavariables in it
    --   * It's just a metavariable itself
    noMeta : Term vs -> Nat -> Bool
    noMeta (App _ f _ a) (S k) = noMeta f k && noMeta a k
    noMeta (Bind _ _ b sc) (S k) = noMeta (binderType b) k && noMeta sc k
    noMeta (Meta {}) d = False
    noMeta (TDelayed _ _ t) d = noMeta t d
    noMeta (TDelay _ _ t a) d = noMeta t d && noMeta a d
    noMeta (TForce _ _ t) d = noMeta t d
    noMeta (As _ _ a p) d = noMeta a d && noMeta p d
    noMeta (Local {}) _ = True
    noMeta (Ref {}) _ = True
    noMeta (PrimVal {}) _ = True
    noMeta (TType {}) _ = True
    noMeta _ _ = False

    isSimple : Term vs -> Bool
    isSimple (Meta {}) = True
    isSimple (Bind _ _ (Lam {}) sc) = isSimple sc
    isSimple (App _ f _ a) = noMeta f 6 && noMeta a 3
    isSimple tm = noMeta tm 0

    updateIVar : forall vs, newvars . IVars vs newvars -> Var newvars ->
                 Maybe (Var vs)
    updateIVar (ICons Nothing rest) new
        = later <$> updateIVar rest new
    updateIVar (ICons (Just old) rest) new
        = if new == old
             then Just first
             else later <$> updateIVar rest new
    updateIVar _ _ = Nothing

    updateIVars : {vs, newvars : _} ->
                  IVars vs newvars -> Term newvars -> Maybe (Term vs)

    updateForced : {vs, newvars : _} ->
                   IVars vs newvars -> List (Var newvars, Term newvars) ->
                   Maybe (List (Var vs, Term vs))
    updateForced ivs [] = Just []
    updateForced ivs ((v, tm) :: ts)
        = case updateIVar ivs v of
               Nothing => updateForced ivs ts
               Just v' => Just ((v', !(updateIVars ivs tm)) ::
                                   !(updateForced ivs ts))

    updateIScope : {vs, newvars : _} ->
                   IVars vs newvars -> CaseScope newvars -> Maybe (CaseScope vs)
    updateIScope ivs (RHS fs tm)
        = Just (RHS !(updateForced ivs fs) !(updateIVars ivs tm))
    updateIScope ivs (Arg c x sc)
        = Just (Arg c x !(updateIScope (ICons (Just (MkVar First))
                                            (weaken ivs)) sc))

    updateIAlts : {vs, newvars : _} ->
                  IVars vs newvars -> CaseAlt newvars -> Maybe (CaseAlt vs)
    updateIAlts ivs (ConCase fc n t sc)
        = Just (ConCase fc n t !(updateIScope ivs sc))
    updateIAlts ivs (DelayCase fc ty arg rhs)
        = let ivs' = ICons (Just (MkVar First)) $
                     ICons (Just (MkVar (Later First))) $
                     weaken (weaken ivs) in
              Just (DelayCase fc ty arg !(updateIVars ivs' rhs))
    updateIAlts ivs (ConstCase fc c rhs)
        = Just (ConstCase fc c !(updateIVars ivs rhs))
    updateIAlts ivs (DefaultCase fc rhs)
        = Just (DefaultCase fc !(updateIVars ivs rhs))

    updateIVars ivs (Local fc r idx p)
        = do MkVar p' <- updateIVar ivs (MkVar p)
             Just (Local fc r _ p')
    updateIVars ivs (Ref fc nt n) = pure $ Ref fc nt n
    updateIVars ivs (Meta fc n i args)
        = pure $ Meta fc n i !(traverse @{Compose} (updateIVars ivs) args)
    updateIVars {vs} ivs (Bind fc x b sc)
        = do b' <- updateIVarsB ivs b
             sc' <- updateIVars (ICons (Just first) (weaken ivs)) sc
             Just (Bind fc x b' sc')
      where
        updateIVarsPi : {vs, newvars : _} ->
                        IVars vs newvars -> PiInfo (Term newvars) -> Maybe (PiInfo (Term vs))
        updateIVarsPi ivs Explicit = Just Explicit
        updateIVarsPi ivs Implicit = Just Implicit
        updateIVarsPi ivs AutoImplicit = Just AutoImplicit
        updateIVarsPi ivs (DefImplicit t)
            = do t' <- updateIVars ivs t
                 Just (DefImplicit t')

        updateIVarsB : {vs, newvars : _} ->
                       IVars vs newvars -> Binder (Term newvars) -> Maybe (Binder (Term vs))
        updateIVarsB ivs (Lam fc c p t)
            = do p' <- updateIVarsPi ivs p
                 Just (Lam fc c p' !(updateIVars ivs t))
        updateIVarsB ivs (Let fc c v t) = Just (Let fc c !(updateIVars ivs v) !(updateIVars ivs t))
        -- Make 'pi' binders have multiplicity W when we infer a Rig1 metavariable,
        -- since this is the most general thing to do if it's unknown.
        updateIVarsB ivs (Pi fc rig p t)
            = do p' <- updateIVarsPi ivs p
                 Just (Pi fc rig p' !(updateIVars ivs t))
        updateIVarsB ivs (PVar fc c p t)
            = do p' <- updateIVarsPi ivs p
                 Just (PVar fc c p' !(updateIVars ivs t))
        updateIVarsB ivs (PLet fc c v t) = Just (PLet fc c !(updateIVars ivs v) !(updateIVars ivs t))
        updateIVarsB ivs (PVTy fc c t) = Just (PVTy fc c !(updateIVars ivs t))
    updateIVars ivs (App fc f c a)
        = Just (App fc !(updateIVars ivs f) c !(updateIVars ivs a))
    updateIVars ivs (As fc u a p)
        = Just (As fc u !(updateIVars ivs a) !(updateIVars ivs p))
    updateIVars ivs (Case fc t c sc scty alts)
        = Just (Case fc t c !(updateIVars ivs sc) !(updateIVars ivs scty)
                      !(traverse (updateIAlts ivs) alts))
    updateIVars ivs (TDelayed fc r arg)
        = Just (TDelayed fc r !(updateIVars ivs arg))
    updateIVars ivs (TDelay fc r ty arg)
        = Just (TDelay fc r !(updateIVars ivs ty) !(updateIVars ivs arg))
    updateIVars ivs (TForce fc r arg)
        = Just (TForce fc r !(updateIVars ivs arg))
    updateIVars ivs (PrimVal fc c) = Just (PrimVal fc c)
    updateIVars ivs (PrimOp fc fn args)
        = Just (PrimOp fc fn !(traverse (updateIVars ivs) args))
    updateIVars ivs (Erased fc Impossible) = Just (Erased fc Impossible)
    updateIVars ivs (Erased fc Placeholder) = Just (Erased fc Placeholder)
    updateIVars ivs (Erased fc (Dotted t)) = Erased fc . Dotted <$> updateIVars ivs t
    updateIVars ivs (Unmatched fc u) = Just (Unmatched fc u)
    updateIVars ivs (TType fc u) = Just (TType fc u)

    mkDef : {vs, newvars : _} ->
            List (Var newvars) ->
            IVars vs newvars -> Term newvars -> Term vs ->
            Core (Maybe (Term vs))
    mkDef (v :: vs) vars soln (Bind bfc x (Pi fc c info ty) sc)
       = do sc' <- mkDef vs (ICons (Just v) vars) soln sc
            pure $ (Bind bfc x (Lam fc c info (Erased bfc Placeholder)) <$> sc')
    mkDef vs vars soln (Bind bfc x b@(Let _ c val ty) sc)
       = do mbsc' <- mkDef vs (ICons Nothing vars) soln sc
            flip traverseOpt mbsc' $ \sc' =>
              case shrink sc' (Drop Refl) of
                Just scs => pure scs
                Nothing => pure $ Bind bfc x b sc'
    mkDef [] vars soln _
       = do let Just soln' = updateIVars vars soln
                | Nothing => ufail loc ("Can't make solution for " ++ show mname
                                           ++ " " ++ show (getIVars vars, soln))
            pure (Just soln')
    mkDef _ _ _ _ = pure Nothing

-- update a solution that the machine found with the thing the programmer
-- actually wrote! We assume that we've already checked that they unify.
export
updateSolution : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Env Term vars -> Term vars -> Term vars -> Core Bool
updateSolution env (Meta fc mname idx args) soln
    = do defs <- get Ctxt
         case !(patternEnvTm env (cast (map snd args))) of
              Nothing => pure False
              Just (newvars ** (locs, submv)) =>
                  case shrink soln submv of
                       Nothing => pure False
                       Just stm =>
                          do Just hdef <- lookupCtxtExact (Resolved idx) (gamma defs)
                                  | Nothing => throw (InternalError "Can't happen: no definition")
                             tryInstantiate fc inTerm env mname idx (length args) hdef (toList locs) soln stm
updateSolution env metavar soln
    = pure False

export
solveIfUndefined : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   Env Term vars -> Term vars -> Term vars -> Core Bool
solveIfUndefined env metavar@(Meta fc mname idx args) soln
    = do defs <- get Ctxt
         Just (Hole {}) <- lookupDefExact (Resolved idx) (gamma defs)
              | _ => pure False
         updateSolution env metavar soln
solveIfUndefined env (Erased _ (Dotted metavar)) soln
  = solveIfUndefined env metavar soln
solveIfUndefined env metavar soln
    = pure False

isDefInvertible : {auto c : Ref Ctxt Defs} ->
                  FC -> Int -> Core Bool
isDefInvertible fc i
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => throw (UndefinedName fc (Resolved i))
         pure (invertible gdef)

spineToValues : Spine vars -> List (Core (Glued vars))
spineToValues sp = toList (map value sp)

mutual
  unifyIfEq : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              (postpone : Bool) ->
              FC -> UnifyInfo -> Env Term vars -> Glued vars -> Glued vars ->
              Core UnifyResult
  unifyIfEq post loc mode env x y
        = do defs <- get Ctxt
             if !(convert env x y)
                then pure success
                else if post
                        then postpone loc mode ("Postponing unifyIfEq " ++
                                                 show (atTop mode)) env x y
                        else convertError loc env x y

  getArgTypes : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                (fnType : NF vars) -> SnocList (Core (Glued vars)) ->
                Core (Maybe (SnocList (Glued vars)))
  getArgTypes (VBind _ n (Pi _ _ _ ty) sc) (as :< a)
     = do Just scTys <- getArgTypes !(expand !(sc a)) as
               | Nothing => pure Nothing
          pure (Just (scTys :< ty))
  getArgTypes _ [<] = pure (Just [<])
  getArgTypes _ _ = pure Nothing

  headsConvert : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 UnifyInfo ->
                 FC -> Env Term vars ->
                 Maybe (SnocList (Glued vars)) -> Maybe (SnocList (Glued vars)) ->
                 Core Bool
  headsConvert mode fc env (Just vs) (Just ns)
      = case (reverse vs, reverse ns) of
             (_ :< v, _ :< n) =>
                do logNF "unify.head" 10 "Unifying head" env v
                   logNF "unify.head" 10 ".........with" env n
                   res <- unify mode fc env v n
                   -- If there's constraints, we postpone the whole equation
                   -- so no need to record them
                   pure (isNil (constraints res ))
             _ => pure False
  headsConvert mode fc env _ _
      = do log "unify.head" 10 "Nothing to convert"
           pure True

  unifyInvertible : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    (swaporder : Bool) ->
                    UnifyInfo -> FC -> Env Term vars ->
                    (metaname : Name) -> (metaref : Int) ->
                    (args : List (RigCount, Core (Glued vars))) ->
                    (sp : Spine vars) ->
                    Maybe (ClosedTerm) ->
                    (Spine vars -> Glued vars) ->
                    Spine vars ->
                    Core UnifyResult
  unifyInvertible swap mode fc env mname mref args sp nty con args'
      = do defs <- get Ctxt
           -- Get the types of the arguments to ensure that the rightmost
           -- argument types match up
           Just vty <- lookupTyExact (Resolved mref) (gamma defs)
                | Nothing => ufail fc ("No such metavariable " ++ show mname)
           vargTys <- getArgTypes !(expand !(nf env (embed vty)))
                                  (reverse (cast (map snd args) ++ map value sp)) --  ++ sp)
           nargTys <- maybe (pure Nothing)
                            (\ty => getArgTypes !(expand !(nf env (embed ty)))
                                                $ reverse (map value args'))
                            nty
           log "unify.invertible" 10 "Unifying invertible vty: \{show vty}, vargTys: \{show $ map asList vargTys}, nargTys: \{show $ map asList nargTys}"
           -- If the rightmost arguments have the same type, or we don't
           -- know the types of the arguments, we'll get on with it.
           if !(headsConvert mode fc env vargTys nargTys)
              then
                -- Unify the rightmost arguments, with the goal of turning the
                -- hole application into a pattern form
                case (sp, args') of
                     (hargs :< h, fargs :< f) =>
                        tryUnify
                          (if not swap then
                              do hv <- value h
                                 fv <- value f
                                 logNF "unify.invertible" 10 "Unifying rightmost" env hv
                                 logNF "unify.invertible" 10 "With rightmost...." env fv
                                 ures <- unify mode fc env hv fv
                                 log "unify.invertible" 10 $ "Constraints " ++ show (constraints ures)
                                 uargs <- unify {f=Normal} mode fc env
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                                (con fargs)
                                 pure (union ures uargs)
                             else
                              do log "unify.invertible" 10 "Unifying invertible"
                                 ures <- unify mode fc env !(value f) !(value h)
                                 log "unify.invertible" 10 $ "Constraints " ++ show (constraints ures)
                                 uargs <- unify {f'=Normal} mode fc env
                                                (con fargs)
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                 pure (union ures uargs))
                          (postponeS {f=Normal} swap fc mode "Postponing hole application [1]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args'))
                     _ => postponeS {f=Normal} swap fc mode "Postponing hole application [2]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args')
              else -- TODO: Cancellable function applications
                   postpone {f=Normal} fc mode "Postponing hole application [3]" env
                            (VMeta fc mname mref args sp (pure Nothing)) (con args')

  -- Unify a hole application - we have already checked that the hole is
  -- invertible (i.e. it's a determining argument to a proof search where
  -- it is a constructor or something else invertible in each case)
  unifyHoleApp : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {vars : _} ->
                 (swaporder : Bool) ->
                 UnifyInfo -> FC -> Env Term vars ->
                 (metaname : Name) -> (metaref : Int) ->
                 (args : List (RigCount, Core (Glued vars))) ->
                 (sp : Spine vars) ->
                 NF vars ->
                 Core UnifyResult
  unifyHoleApp swap mode fc env mname mref args sp (VTCon nfc n a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible swap (lower mode) fc env mname mref args sp mty (VTCon nfc n a) args'
  unifyHoleApp swap mode fc env mname mref args sp (VDCon nfc n t a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible swap (lower mode) fc env mname mref args sp mty (VDCon nfc n t a) args'
  unifyHoleApp swap mode loc env mname mref args sp (VLocal nfc idx p args')
      = unifyInvertible swap (lower mode) loc env mname mref args sp Nothing (VLocal nfc idx p) args'
  unifyHoleApp swap mode fc env mname mref args sp tm@(VMeta nfc n i margs2 args2' val)
      = do defs <- get Ctxt
           Just mdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => undefinedName nfc mname
           let inv = isPatName n || invertible mdef
           if inv
              then unifyInvertible swap (lower mode) fc env mname mref args sp Nothing
                                   (\t => VMeta nfc n i margs2 t val) args2'
              else postponeS {f=Normal} swap fc mode "Postponing hole application" env
                             (VMeta fc mname mref args sp (pure Nothing)) (asGlued tm)
    where
      isPatName : Name -> Bool
      isPatName (PV {}) = True
      isPatName _ = False
  unifyHoleApp swap mode fc env mname mref args sp tm
      = postponeS {f=Normal} swap fc mode "Postponing hole application" env
                  (VMeta fc mname mref args sp (pure Nothing)) (asGlued tm)

  postponePatVar : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   {vars : _} ->
                   (swaporder : Bool) ->
                   UnifyInfo -> FC -> Env Term vars ->
                   (metaname : Name) -> (metaref : Int) ->
                   (margs : List (RigCount, Core (Glued vars))) ->
                   (margs' : Spine vars) ->
                   (soln : Glued vars) ->
                   Core UnifyResult
  postponePatVar swap mode fc env mname mref margs margs' tm
      = do let x = VMeta fc mname mref margs margs' (pure Nothing)
           if !(convert env x tm)
              then pure success
              else postponeS {f=Normal} swap fc mode "Not in pattern fragment" env
                             x tm

  -- Solve a metavariable application (that is, the name applied the to
  -- args and spine) with the given solution.
  -- Also given the results we got from 'patternEnv' that tells us how to
  -- instantiate the environment in the solution
  solveHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {newvars, vars : _} ->
              FC -> UnifyInfo -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Core (Glued vars))) ->
              (sp : Spine vars) ->
              SnocList (Var newvars) ->
              Thin newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : Glued vars) ->
              Core (Maybe UnifyResult)
  solveHole fc mode env mname mref margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           ust <- get UST
           if solutionHeadSame !(expand solnf) || inNoSolve mref (noSolve ust)
              then pure $ Just success
              else do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                           | Nothing => throw (InternalError ("Can't happen: Lost hole " ++ show mname))
                      progress <- tryInstantiate fc mode env mname mref (length margs) hdef (toList locs) solfull stm
                      pure $ toMaybe progress (solvedHole mref)
    where
      inNoSolve : Int -> IntMap () -> Bool
      inNoSolve i ns
          = case lookup i ns of
                 Nothing => False
                 Just _ => True

      -- Only need to check the head metavar is the same, we've already
      -- checked the rest if they are the same (and we couldn't instantiate it
      -- anyway...)
      -- Also the solution is expanded by now (via Evaluate.Value.expand)
      solutionHeadSame : NF vars -> Bool
      solutionHeadSame (VMeta _ _ shead _ _ _) = shead == mref
      solutionHeadSame _ = False

  unifyHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              (swaporder : Bool) ->
              UnifyInfo -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Core (Glued vars))) ->
              (sp : Spine vars) ->
              (soln : Glued vars) ->
              Core UnifyResult
  unifyHole swap mode fc env nfc mname mref args sp tmnf
      = do let margs = cast !(traverse snd args)
           margs' <- traverseSnocList value sp
           let pargs = if isLin margs' then margs else margs ++ margs'
           logC "unify.hole" 10
                   (do -- [Note] Restore logging sequence
                       qargs <- map reverse $ traverse (quote env) (reverse margs')
                       qtm <- quote env tmnf
                       pure $ "Unifying: " ++ show !(toFullNames mname) ++ " " ++ show !(traverse toFullNames qargs) ++
                              " with " ++ show !(toFullNames qtm)) -- first attempt, try 'empty', only try 'defs' when on 'retry'?
           defs <- get Ctxt
           logNF "elab" 10 ("Trying to solve " ++ show mname ++ " with") env tmnf
           logC "unify.hole" 10
                   (do qargs <- logQuiet $ traverse (quote env) pargs
                       qtm <- logQuiet $ quote env tmnf
                       pure $ "Unifying: " ++ show mname ++ " args " ++ show qargs ++
                              " with " ++ show qtm) -- first attempt, try 'empty', only try 'defs' when on 'retry'?
           case !(patternEnv env pargs) of
                Nothing =>
                  do log "unify.hole" 10 $ "unifyHole patEnv: Nothing"
                     Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ _ = definition hdef
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     if invertible hdef
                        then unifyHoleApp swap mode fc env mname mref args sp !(expand tmnf)
                        else postponePatVar swap mode fc env mname mref args sp tmnf
                Just (newvars ** (locs, submv)) =>
                  do log "unify.hole" 10 $ "unifyHole patEnv newvars: \{show $ asList newvars}, locs: \{show locs}, submv: \{show submv}"
                     Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                         | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ _ = definition hdef
                         | wat => postponeS {f=Normal} swap fc mode "Delayed hole" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     tm <- quote env tmnf
                     Just tm <- occursCheck fc env mode mname tm
                         | _ => postponeS {f=Normal} swap fc mode "Occurs check failed" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     let solveOrElsePostpone : Term newvars -> Core UnifyResult
                         solveOrElsePostpone stm = do
                           mbResult <- solveHole fc mode env mname mref
                                                 args sp locs submv
                                                 tm stm tmnf
                           flip fromMaybe (pure <$> mbResult) $
                             postponeS {f=Normal} swap fc mode "Can't instantiate" env
                                       (VMeta fc mname mref args sp (pure Nothing))
                                       tmnf
                     case shrinkTerm tm submv of
                          Just stm => solveOrElsePostpone stm
                          Nothing =>
                            do tm' <- quoteNF env tmnf
                               case shrinkTerm tm' submv of
                                    Nothing => postponeS {f=Normal} swap fc mode "Can't shrink" env
                                                         (VMeta fc mname mref args sp (pure Nothing))
                                                         tmnf
                                    Just stm => solveOrElsePostpone stm

  -- Main bit of unification, decomposing unification problems into
  -- sub-problems and solving metavariables where appropriate
  unifyNoEta : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               UnifyInfo -> FC -> Env Term vars ->
               Value f vars -> Value f' vars -> Core UnifyResult

  unifyNotMetavar : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyInfo -> FC -> Env Term vars ->
                    Value f vars -> Value f' vars -> Core UnifyResult
  -- Unifying applications means we're stuck and need to postpone, since we've
  -- already checked convertibility
  -- In 'match' or 'search'  mode, we can nevertheless unify the arguments
  -- if the names match.
  unifyNotMetavar mode@(MkUnifyInfo p InSearch) fc env x@(VApp _ _ nx spx _) y@(VApp _ _ ny spy _)
      = if nx == ny
           then do logC "unify.application" 5
                          (do xs' <- logQuiet $ traverse value spx
                              xs <- logQuiet $ traverse (quote env) xs'
                              yx' <- logQuiet $ traverse value spy
                              ys <- logQuiet $ traverse (quote env) yx'
                              pure ("Searching args " ++ show xs ++ " " ++ show ys))
                   unifySpine mode fc env spx spy
           else postpone fc mode "Postponing application (search)" env x y
  unifyNotMetavar mode@(MkUnifyInfo p InMatch) fc env x@(VApp _ _ nx spx _) y@(VApp _ _ ny spy _)
      = if nx == ny
           then do logC "unify.application" 5
                          (do xs' <- logQuiet $ traverse value spx
                              xs <- logQuiet $ traverse (quote env) xs'
                              yx' <- logQuiet $ traverse value spy
                              ys <- logQuiet $ traverse (quote env) yx'
                              pure ("Matching args " ++ show xs ++ " " ++ show ys))
                   unifySpine mode fc env spx spy
           else postpone fc mode "Postponing application (match)" env x y
  -- Now the cases where we're decomposing into smaller problems
  unifyNotMetavar mode fc env x@(VLocal fcx idx _ [<]) y@(VLocal fcy idy _ [<])
      = if idx == idy
           then pure success
           else convertError fc env x y
  unifyNotMetavar mode@(MkUnifyInfo p InTerm) fc env x@(VLocal fcx idx _ spx)
                                                     y@(VLocal fcy idy _ spy)
      = if idx == idy
           then unifySpine mode fc env spx spy
           else postpone fc mode "Postponing local app" env x y
  unifyNotMetavar mode@(MkUnifyInfo p InMatch) fc env x@(VLocal fcx idx _ spx)
                                                      y@(VLocal fcy idy _ spy)
      = if idx == idy
           then unifySpine mode fc env spx spy
           else postpone fc mode "Postponing local app" env x y
  unifyNotMetavar mode fc env x@(VDCon fcx nx tx ax spx) y@(VDCon fcy ny ty ay spy)
      = do logC "unify" 20 $ do
             x <- toFullNames nx
             y <- toFullNames ny
             pure $ "Comparing data constructors " ++ show x ++ " and " ++ show y
           if tx == ty
             then unifySpine mode fc env spx spy
             else convertError fc env x y
  unifyNotMetavar mode fc env x@(VTCon fcx nx ax spx) y@(VTCon fcy ny ay spy)
      = do logC "unify" 20 $ do
             x <- toFullNames nx
             y <- toFullNames ny
             pure $ "Comparing type constructors " ++ show x ++ " and " ++ show y
           if nx == ny
             then do logC "unify" 20 $
                       pure $ "Constructor " ++ show !(toFullNames nx)
                     logC "unify" 20 $ map (const "") $
                        traverse_ dumpArg (map value spx)
                     logC "unify" 20 $ map (const "") $
                        traverse_ dumpArg (map value spy)
                     unifySpineMetaArg mode fc env spx spy
             else convertError fc env x y
      where
        dumpArg : Core (Glued vars) -> Core ()
        dumpArg v = do
          v' <- logQuiet $ do nf env !(quote env !v)
          logNF "unify" 20 "NF" env v'
          logC "unify" 50 $ pure "NF Show: \{show v'}"

  unifyNotMetavar mode fc env (VDelayed _ _ x) (VDelayed _ _ y)
      = unify (lower mode) fc env x y
  unifyNotMetavar mode fc env (VDelay _ _ tx ax) (VDelay _ _ ty ay)
      = unifyArgs (lower mode) fc env [pure tx,pure ax] [pure ty,pure ay]
  unifyNotMetavar mode fc env (VForce _ _ vx spx) (VForce _ _ vy spy)
      = do cs <- unify (lower mode) fc env vx vy
           cs' <- unifySpine (lower mode) fc env spx spy
           pure (union cs cs')
  unifyNotMetavar mode fc env x@(VCase{}) y@(VCase{})
      = unifyIfEq True fc mode env (asGlued x) (asGlued y)
  unifyNotMetavar mode fc env x@(VApp{}) y
      -- conversion check first, in case app is a blocked case
      = do logC "unify" 20 $ do
             x <- logQuiet $ quote env x
             x <- toFullNames x
             y <- logQuiet $ quote env y
             y <- toFullNames y
             pure $ "Comparing left application to right something: " ++ show x ++ " and " ++ show y
           if !(convert env x y)
              then pure success
              else postpone fc mode "Postponing application (left)" env x y
  unifyNotMetavar mode fc env x y@(VApp{})
      = do logC "unify" 20 $ do
             x <- logQuiet $ quote env x
             x <- toFullNames x
             y <- logQuiet $ quote env y
             y <- toFullNames y
             pure $ "Comparing right application to left something: " ++ show y ++ " and " ++ show x
           if !(convert env x y)
              then pure success
              else postpone fc mode "Postponing application (right)" env x y
  unifyNotMetavar mode fc env (VAs _ _ _ x) y = unifyNoEta mode fc env !(expand x) y
  unifyNotMetavar mode fc env x (VAs _ _ _ y) = unifyNoEta mode fc env x !(expand y)
  unifyNotMetavar mode fc env x_in y_in
      = do x <- expand x_in
           y <- expand y_in
           log "unify.noeta" 10 $ "Nothing else worked, unifyIfEq"
           unifyIfEq (isPostponable x || isPostponable y) fc mode env (asGlued x) (asGlued y)
    where
      -- If one of them is a delay, and they're not equal, we'd better
      -- postpone and come back to it so we can insert the implicit
      -- Force/Delay later
      isPostponable : NF vars -> Bool
      isPostponable (VDelayed{}) = True
      isPostponable (VCase{}) = True
      isPostponable (VForce{}) = True
      isPostponable _ = False

  -- Deal with metavariable cases first
  -- If they're both holes, solve the one with the bigger context
  unifyNoEta mode fc env x@(VMeta fcx nx ix margsx argsx _) y@(VMeta fcy ny iy margsy argsy _)
      = do -- First check if they're convertible already, in which case
           -- we've won already
           log "elab" 10 ("Unifying metas " ++ show nx ++ " and " ++ show ny)
           False <- convert env x y
                | _ => pure success
           invx <- isDefInvertible fc ix
           if ix == iy && (invx || umode mode == InSearch)
                               -- Invertible, (from auto implicit search)
                               -- so we can also unify the arguments.
              then unifyArgs mode fc env
                             ((map snd margsx) ++ (spineToValues argsx))
                             ((map snd margsy) ++ (spineToValues argsy))
              else do xvs <- traverse (\ (c, t) => pure (c, asGlued !(expand !t))) margsx
                      yvs <- traverse (\ (c, t) => pure (c, asGlued !(expand !t))) margsy
                      let xlocs = localsIn (map snd xvs)
                      let ylocs = localsIn (map snd yvs)
                      -- Solve the one with the bigger context, and if they're
                      -- equal, the one that's applied to fewest things (because
                      -- then the arguments get substituted in)
                      let xbigger = xlocs > ylocs
                                      || (xlocs == ylocs &&
                                           length argsx <= length argsy)
                      if (xbigger || umode mode == InMatch) && not (pv nx)
                         then unifyHole False mode fc env fcx nx ix (map toCore xvs) argsx (asGlued y)
                         else unifyHole True mode fc env fcy ny iy (map toCore yvs) argsy (asGlued x)
    where
      toCore : (a, b) -> (a, Core b)
      toCore (x, y) = (x, pure y)

      pv : Name -> Bool
      pv (PV {}) = True
      pv _ = False

      localsIn : forall f . List (Value f vars) -> Nat
      localsIn [] = 0
      localsIn (VLocal {} :: xs) = 1 + localsIn xs
      localsIn (_ :: xs) = localsIn xs
  unifyNoEta mode fc env (VErased _ (Dotted x)) (VErased _ (Dotted y))
      = unifyNoEta mode fc env !(expand x) !(expand y)
  unifyNoEta mode fc env x (VErased _ (Dotted y))
      = unifyNoEta mode fc env x !(expand y)
  unifyNoEta mode fc env (VErased _ (Dotted x)) y
      = unifyNoEta mode fc env !(expand x) y
  unifyNoEta mode fc env (VMeta fcm n i margs args _) tm
      = unifyHole False mode fc env fcm n i margs args (asGlued tm)
  unifyNoEta mode fc env tm (VMeta fcm n i margs args _)
      = unifyHole True mode fc env fcm n i margs args (asGlued tm)
  unifyNoEta mode fc env tm tm' = unifyNotMetavar mode fc env tm tm'

  mkArgVar : FC -> Name -> Glued vars
  mkArgVar fc var = vRef fc Bound var

  mkArg : FC -> Name -> Core (Glued vars)
  mkArg fc var = pure $ mkArgVar fc var


  unifyPiInfo : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {vars : _} ->
                UnifyInfo -> FC -> Env Term vars ->
                PiInfo (Glued vars) -> PiInfo (Glued vars) ->
                Core (Maybe UnifyResult)
  unifyPiInfo mode loc env Explicit Explicit = pure $ Just success
  unifyPiInfo mode loc env Implicit Implicit = pure $ Just success
  unifyPiInfo mode loc env AutoImplicit AutoImplicit = pure $ Just success
  unifyPiInfo mode loc env (DefImplicit x) (DefImplicit y) = Just <$> unify mode loc env x y
  unifyPiInfo mode loc env _ _ = pure Nothing

  unifyBothBinders: {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyInfo -> FC -> Env Term vars ->
                    FC -> Name -> Binder (Glued vars) ->
                    (Core (Glued vars) -> Core (Glued vars)) ->
                    FC -> Name -> Binder (Glued vars) ->
                    (Core (Glued vars) -> Core (Glued vars)) ->
                    Core UnifyResult
  unifyBothBinders mode fc env fcx nx bx@(Pi bfcx cx ix tx) scx fcy ny by@(Pi bfcy cy iy ty) scy
      = let err = convertGluedError fc env
                 (VBind fcx nx bx scx)
                 (VBind fcy ny by scy)
        in if cx /= cy
          then err
          else do Just ci <- unifyPiInfo (lower mode) fc env ix iy
                    | Nothing => err
                  csarg <- unify (lower mode) fc env tx ty
                  tx' <- quote env tx
                  x' <- genVarName "x"
                  logTerm "unify.binder" 10 "Unifying arg" tx'
                  logNF "unify.binder" 10 "........with" env ty
                  let env' : Env Term (_ :< nx)
                           = env :< Pi fcy cy Explicit tx'
                  logEnv "unify.binder" 10 "env'" env'
                  logC "unify.binder" 10 $ pure "Unifying pi \{show ix} and \{show iy}"
                  case constraints csarg of
                      [] => -- No constraints, check the scope
                         do tscx <- scx (mkArg fc x')
                            logNF "unify.binder" 10 "tscx" env tscx
                            tscy <- scy (mkArg fc x')
                            logNF "unify.binder" 10 "tscy" env tscy
                            tmx <- quote env tscx
                            tmy <- quote env tscy
                            logTermNF "unify.binder" 10 "Unifying scope" env tmx
                            logTermNF "unify.binder" 10 "..........with" env tmy
                            logTermNF "unify.binder" 10 "refsToLocals: Unifying scope" env' (refsToLocals (Add nx x' None) tmx)
                            logTermNF "unify.binder" 10 "refsToLocals: ..........with" env' (refsToLocals (Add nx x' None) tmy)
                            cs <- unify (lower mode) fc env'
                              (refsToLocals (Add nx x' None) tmx)
                              (refsToLocals (Add nx x' None) tmy)
                            pure (union ci cs)
                      cs => -- Constraints, make new constant
                         do txtm <- quote env tx
                            tytm <- quote env ty
                            c <- newConstant fc erased env
                                   (Bind fcx nx (Lam fcy cy Explicit txtm) (Local fcx Nothing _ First))
                                   (Bind fcx nx (Pi fcy cy Explicit txtm)
                                       (weaken tytm)) cs
                            tscx <- scx (mkArg fc x')
                            tscy <- scy (mkArg fc x')
                            tmx <- quote env tscx
                            tmy <- quote env tscy
                            cs' <- unify (lower mode) fc env'
                                     (refsToLocals (Add nx x' None) tmx)
                                     (refsToLocals (Add nx x' None) tmy)
                            pure (union ci (union csarg cs'))
  unifyBothBinders mode fc env xfc nx bx@(Lam fcx cx ix tx) scx yfc ny by@(Lam fcy cy iy ty) scy
      = let err = convertGluedError fc env
                 (VBind fcx nx bx scx)
                 (VBind fcy ny by scy)
        in if cx /= cy
          then err
          else do Just ci <- unifyPiInfo (lower mode) fc env ix iy
                    | Nothing => err
                  ct <- unify (lower mode) fc env tx ty
                  xn <- genVarName "x"
                  txtm <- quote env tx
                  let env' : Env Term (_ :< nx)
                           = env :< Lam fcx cx Explicit txtm

                  tscx <- scx (mkArg fc xn)
                  tscy <- scy (mkArg fc xn)
                  tmx <- quote env tscx
                  tmy <- quote env tscy
                  cs' <- unify (lower mode) fc env'
                           (refsToLocals (Add nx xn None) tmx)
                           (refsToLocals (Add nx xn None) tmy)
                  pure (union ci (union ct cs'))
  unifyBothBinders mode fc env fcx nx bx scx fcy ny by scy
      = convertGluedError fc env
                  (VBind fcx nx bx scx)
                  (VBind fcy ny by scy)

  isHoleApp : NF vars -> Bool
  isHoleApp (VMeta{}) = True
  isHoleApp _ = False

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyWithEta : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {vars : _} ->
                 UnifyInfo -> FC -> Env Term vars ->
                 NF vars -> NF vars -> Core UnifyResult
  -- Pair of binders or lambdas
  unifyWithEta mode fc env x@(VBind _ nx (Lam fcx cx ix tx) scx) y@(VBind _ ny (Lam _ cy iy ty) scy)
      = if cx /= cy
          then convertError fc env x y
          else do ct <- unify (lower mode) fc env tx ty
                  var <- genVarName "x"
                  txtm <- quote env tx
                  let env' : Env Term (_ :< nx)
                           = env :< Lam fcx cx Explicit txtm
                  tscx <- scx $ pure $ mkArgVar fc var
                  tscy <- scy $ pure $ mkArgVar fc var
                  tmx <- quote env tscx
                  tmy <- quote env tscy
                  logTerm "unify.binder" 10 "Unifying lambda scope" tmx
                  logTerm "unify.binder" 10 ".................with" tmy
                  cs' <- unify (lower mode) fc env'
                               (refsToLocals (Add nx var None) tmx)
                               (refsToLocals (Add nx var None) tmy)
                  pure (union ct cs')

  -- Eta rules
  unifyWithEta mode fc env tmx@(VBind fcx x (Lam bfc cx ix tx) scx) tmy
        = do logNF "unify" 10 "EtaR" env tmx
             logNF "unify" 10 "...with" env tmy
             if isHoleApp tmy
                then if not !(convert env tmx tmy)
                        then unifyNoEta (lower mode) fc env tmx tmy
                        else pure success
                else do domty <- quote env tx
                        etay <- nf env
                                  $ Bind fcx x (Lam bfc cx Explicit domty)
                                  $ App fcx (weaken !(quote env tmy))
                                            cx
                                            (Local fcx Nothing 0 First)
                        logNF "unify" 10 "Expand" env etay
                        unify (lower mode) fc env tmx etay
  unifyWithEta mode fc env tmx tmy@(VBind fcy y (Lam bfc cy iy ty) scy)
        = do logNF "unify" 10 "EtaR" env tmx
             logNF "unify" 10 "...with" env tmy
             if isHoleApp tmx
                then if not !(convert env tmx tmy)
                        then unifyNoEta (lower mode) fc env tmx tmy
                        else pure success
                else do domty <- quote env ty
                        etax <- nf env
                                  $ Bind fcy y (Lam bfc cy Explicit domty)
                                  $ App fcy (weaken !(quote env tmx))
                                            cy
                                            (Local fcy Nothing 0 First)
                        logNF "unify" 10 "Expand" env etax
                        unify (lower mode) fc env etax tmy
  unifyWithEta mode fc env (VBind fcx nx bx scx) (VBind fcy ny by scy)
      = unifyBothBinders mode fc env fcx nx bx scx fcy ny by scy
  unifyWithEta mode fc env x y
      = unifyNoEta mode fc env x y

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyLazy : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              UnifyInfo -> FC -> Env Term vars ->
              NF vars -> NF vars -> Core UnifyResult
  unifyLazy mode fc env (VDelayed _ _ x) (VDelayed _ _ y)
      = unifyWithEta (lower mode) fc env !(expand x) !(expand y)
  unifyLazy mode fc env x@(VDelayed _ r tmx) tmy
      = if isHoleApp tmy && not (umode mode == InMatch)
           then postpone fc mode "Postponing in lazy" env x tmy
           else do logNF "unify" 5 "Add force" env tmx
                   vs <- unify (lower mode) fc env tmx tmy
                   pure ({ addLazy := AddForce r } vs)
  unifyLazy mode fc env tmx (VDelayed _ r tmy)
      = do vs <- unify (lower mode) fc env tmx tmy
           pure ({ addLazy := AddDelay r } vs)
  unifyLazy mode fc env x y = unifyWithEta mode fc env x y

  -- First, see if we need to evaluate VApp a bit more
  -- Also, if we have two VApps that immediately convert without reduction,
  -- take advantage of that
  unifyExpandApps : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    Bool ->
                    UnifyInfo -> FC -> Env Term vars ->
                    Glued vars -> Glued vars -> Core UnifyResult
  -- If the values convert already, we're done
  unifyExpandApps lazy mode fc env x@(VApp fcx ntx nx spx _) y@(VApp fcy nty ny spy _)
      = if nx == ny
           then do inf <- getInfPos nx
                   logC "unify.equal" 10 $
                                do x <- toFullNames nx
                                   y <- toFullNames ny
                                   xs' <- logQuiet $ traverse value spx
                                   xs <- logQuiet $ traverse (quote env) xs'
                                   yx' <- logQuiet $ traverse value spy
                                   ys <- logQuiet $ traverse (quote env) yx'
                                   pure $ "Attempt to convertSpine (func equal already): \{show x} (\{show !(toFullNames xs)}) and \{show y} (\{show !(toFullNames ys)}) \n with inf: \{show inf}"
                   let spx' = NatSet.SnocList.drop inf spx
                   let spy' = NatSet.SnocList.drop inf spy
                   unless (NatSet.isEmpty inf)
                     $ logC "unify.equal" 10 $
                                do xs' <- logQuiet $ traverse value spx'
                                   xs <- logQuiet $ traverse (quote env) xs'
                                   yx' <- logQuiet $ traverse value spy'
                                   ys <- logQuiet $ traverse (quote env) yx'
                                   pure $ "Inferred arguments (\{show inf}) are considered safe to be dropped from convert: (\{show !(toFullNames xs)}) and (\{show !(toFullNames ys)})"
                   c <- convertSpine fc env spx' spy'
                   if c
                      then
                        do logC "unify.equal" 10 $
                                do x <- toFullNames nx
                                   y <- toFullNames ny
                                   pure $ "Skipped unification (equal already): \{show x} and \{show y}"
                           pure success
                      else do valx' <- expand x
                              valy' <- expand y
                              logC "unify.equal" 10 $
                                do x <- toFullNames valx'
                                   y <- toFullNames valy'
                                   pure $ "Begin unification (non-convertable) \{show lazy}: \{show x} and \{show y}"
                              if lazy
                                then unifyLazy mode fc env valx' valy'
                                else unifyWithEta mode fc env valx' valy'
           else do valx' <- expand x
                   valy' <- expand y
                   logC "unify.equal" 10 $
                     do valx' <- toFullNames valx'
                        valy' <- toFullNames valy'
                        pure $ "Begin unification (func non-equal) \{show lazy} \{show mode}: \{show valx'} (from \{show x}) and \{show valy'} (from \{show y})"
                   if lazy
                      then unifyLazy mode fc env valx' valy'
                      else unifyWithEta mode fc env valx' valy'
      where
          getInfPos : Name -> Core NatSet
          getInfPos n
              = do defs <- get Ctxt
                   Just gdef <- lookupCtxtExact n (gamma defs)
                       | _ => pure NatSet.empty
                   pure (inferrable gdef)

          dropInf : Nat -> Nat -> List Nat -> SnocList (SpineEntry a) -> SnocList (SpineEntry a)
          dropInf _ _ [] xs = xs
          dropInf _ _ _ [<] = [<]
          dropInf a i ds (xs :< x)
              = if (a `minus` i) `elem` ds
                   then dropInf a (S i) ds xs
                   else dropInf a (S i) ds xs :< x

  -- Same quick check for metavars
  unifyExpandApps {vars} lazy mode fc env x@(VMeta fcx nx ix scx spx _) y@(VMeta fcy ny iy scy spy _)
      = do True <- do let True = ix == iy
                           | False => pure False
                      True <- convertSpine fc env spx spy
                           | False => pure False
                      convScope scx scy
              | False => do valx' <- expand x
                            valy' <- expand y
                            if lazy
                              then unifyLazy mode fc env valx' valy'
                              else unifyWithEta mode fc env valx' valy'
           pure success
    where
      convScope : List (RigCount, Core (Glued vars)) ->
                  List (RigCount, Core (Glued vars)) -> Core Bool
      convScope [] [] = pure True
      convScope ((_, x) :: xs) ((_, y) :: ys)
          = do True <- convert env !x !y | False => pure False
               convScope xs ys
      convScope _ _ = pure False
  -- Otherwise, make sure the top level thing is expanded (so not a reducible
  -- VApp or VMeta node) then move on
  unifyExpandApps lazy mode fc env x y
      = do logC "unify.equal" 10 $
             do x <- logQuiet $ quote env x
                x <- toFullNames x
                y <- logQuiet $ quote env y
                y <- toFullNames y
                pure $ "Begin unification (non-application) \{show lazy}: \{show x} and \{show y}"
           x' <- expand x
           y' <- expand y
           logC "unify.equal" 10 $
             do x <- logQuiet $ quote env x'
                x <- toFullNames x
                y <- logQuiet $ quote env y'
                y <- toFullNames y
                pure $ "Begin unification (non-application) \{show lazy} expanded: \{show x} and \{show y}"
           if lazy
              then unifyLazy mode fc env x' y'
              else unifyWithEta mode fc env x' y'

  -- Start by expanding any top level Apps (if they don't convert already)
  -- then invoke full unification, either inserting laziness coercions
  -- or not.

  unifyVal : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             UnifyInfo -> FC -> Env Term vars ->
             Glued vars -> Glued vars -> Core UnifyResult
  unifyVal mode fc env x y = logDepth $ unifyExpandApps False mode fc env x y

  unifyValLazy : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {vars : _} ->
                 UnifyInfo -> FC -> Env Term vars ->
                 Glued vars -> Glued vars -> Core UnifyResult
  unifyValLazy mode fc env x y = logDepth $ unifyExpandApps True mode fc env x y

  -- The interesting top level case, for unifying values
  Core.Unify.Value.unify mode fc env x y
     = logDepth $ unifyVal mode fc env (asGlued x) (asGlued y)

  -- The interesting top level case, for unifying values and inserting laziness
  -- coercions if appropriate
  Core.Unify.Value.unifyWithLazy mode fc env x y
     = logDepth $ unifyValLazy mode fc env (asGlued x) (asGlued y)

  Core.Unify.Term.unify umode fc env x y
     = do x' <- logQuiet $ nf env x
          y' <- logQuiet $ nf env y
          unify umode fc env x' y'

  Core.Unify.Term.unifyWithLazy umode fc env x y
     = do x' <- logQuiet $ nf env x
          y' <- logQuiet $ nf env y
          unifyWithLazy umode fc env x' y'

  export
  Unify NF where
    unifyD _ _ mode fc env x y
      = logDepth $ unifyVal mode fc env (asGlued x) (asGlued y)

    unifyWithLazyD _ _ mode fc env x y
      = logDepth $ unifyValLazy mode fc env (asGlued x) (asGlued y)

  export
  Unify Term where
    unifyD _ _ umode fc env x y
      = do x' <- logQuiet $ nf env x
           y' <- logQuiet $ nf env y
           unify umode fc env x' y'
    unifyWithLazyD _ _ umode fc env x y
      = do x' <- logQuiet $ nf env x
           y' <- logQuiet $ nf env y
           unifyWithLazy umode fc env x' y'

  export
  Unify Glued where
    unifyD _ _ mode fc env x y
      = logDepth $ unifyVal mode fc env x y

    unifyWithLazyD _ _ mode fc env x y
      = logDepth $ unifyValLazy mode fc env x y

export
setInvertible : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core ()
setInvertible fc n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         ignore $ addDef n ({ invertible := True } gdef)

public export
data SolveMode = Normal -- during elaboration: unifies and searches
               | Defaults -- unifies and searches for default hints only
               | MatchArgs -- match rather than unify
               | LastChance -- as normal, but any failure throws rather than delays

Eq SolveMode where
  Normal == Normal = True
  Defaults == Defaults = True
  LastChance == LastChance = True
  _ == _ = False


retry : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        UnifyInfo -> Int -> Core UnifyResult
retry mode c
    = do ust <- get UST
         case lookup c (constraints ust) of
              Nothing => pure success
              Just Resolved => pure success
              Just (MkConstraint loc withLazy env xold yold)
               => do defs <- get Ctxt
                     x <- logQuiet $ nf env xold
                     y <- logQuiet $ nf env yold
                     log "unify.retry" 10 (show loc)
                     logNF "unify.retry" 5 ("Retrying " ++ show c ++ " " ++ show (umode mode))
                           env x
                     logNF "unify.retry" 5 "....with" env y
                     log "unify.retry" 5 $ if withLazy
                                then "(lazy allowed)"
                                else "(no lazy)"

                     catch
                       (do cs <- ifThenElse withLazy
                                    (unifyWithLazy mode loc env x y)
                                    (unify (lower mode) loc env x y)
                           logC "unify.retry" 5 $ pure "....result: \{show cs}"
                           case constraints cs of
                             [] => do log "unify.retry" 5 $ "Success " ++ show (addLazy cs)
                                      deleteConstraint c
                                      pure cs
                             _ => do log "unify.retry" 5 $ "Constraints " ++ show (addLazy cs)
                                     pure cs)
                      (\err => do defs <- get Ctxt
                                  throw (WhenUnifying loc (gamma defs) env
                                                      !(quote env x)
                                                      !(quote env y) err))

delayMeta : {vars : _} ->
            LazyReason -> Nat -> Term vars -> Term vars -> Term vars
delayMeta r (S k) ty (Bind fc n b sc)
    = Bind fc n b (delayMeta r k (weaken ty) sc)
delayMeta r envb ty tm = TDelay (getLoc tm) r ty tm

forceMeta : LazyReason -> Nat -> Term vars -> Term vars
forceMeta r (S k) (Bind fc n b sc)
    = Bind fc n b (forceMeta r k sc)
forceMeta r envb tm = TForce (getLoc tm) r tm

-- Check whether it's worth trying a search again, based on what went wrong
recoverable : Error -> Bool
recoverable (UndefinedName {}) = False
recoverable (InType _ _ err) = recoverable err
recoverable (InCon _ err) = recoverable err
recoverable (InLHS _ _ err) = recoverable err
recoverable (InRHS _ _ err) = recoverable err
recoverable (WhenUnifying _ _ _ _ _ err) = recoverable err
recoverable (MaybeMisspelling err _) = recoverable err
recoverable _ = True

-- Retry the given constraint, return True if progress was made
retryGuess : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyInfo -> (smode : SolveMode) -> (hole : (Int, (FC, Name))) ->
             Core Bool
retryGuess mode smode (hid, (loc, hname))
    = do defs <- get Ctxt
         case !(lookupCtxtExact (Resolved hid) (gamma defs)) of
           Nothing => pure False
           Just def =>
             case definition def of
               BySearch rig depth defining =>
                  handleUnify
                     (do tm <- search loc rig (smode == Defaults) depth defining
                                      (type def) Env.empty
                         let pi = if isErased rig
                                    then defaultPI
                                    else reducePI
                         let gdef = { definition := Function pi tm tm Nothing } def
                         logTermNF "unify.retry" 5 ("Solved " ++ show hname) Env.empty tm
                         ignore $ addDef (Resolved hid) gdef
                         removeGuess hid
                         pure True)
                     $ \case
                       DeterminingArg _ n i _ _ =>
                         do logTerm "unify.retry" 5
                                    ("Failed (det " ++ show hname ++ " " ++ show n ++ ")")
                                    (type def)
                            setInvertible loc (Resolved i)
                            pure False -- progress not made yet!
                       err =>
                         do logTermNF "unify.retry" 5
                                      ("Search failed at " ++ show rig ++ " for " ++ show hname ++ " err: " ++ show err)
                                      Env.empty (type def)
                            case smode of
                                 LastChance => throw err
                                 _ => if recoverable err
                                         then pure False -- Postpone again
                                         else throw (CantSolveGoal loc (gamma defs)
                                                        Env.empty (type def) (Just err))
               -- TODO: Check if this is still needed as a performance
               -- hack
               Guess tm envb [constr] =>
                 do let umode = case smode of
                                     MatchArgs => inMatch
                                     _ => mode
                    cs <- retry umode constr
                    case constraints cs of
                         [] => do tm' <- case addLazy cs of
                                           NoLazy => pure tm
                                           AddForce r => pure $ forceMeta r envb tm
                                           AddDelay r =>
                                              do logTerm "unify.retry" 5 "Retry Delay" tm
                                                 pure $ delayMeta r envb (type def) tm
                                  let gdef = { definition := Function reducePI tm' tm' Nothing } def
                                  logTerm "unify.retry" 5 ("Resolved " ++ show hname) tm'
                                  ignore $ addDef (Resolved hid) gdef
                                  removeGuess hid
                                  pure (holesSolved cs)
                         newcs => do tm' <- case addLazy cs of
                                           NoLazy => pure tm
                                           AddForce r => pure $ forceMeta r envb tm
                                           AddDelay r =>
                                              do logTerm "unify.retry" 5 "Retry Delay (constrained)" tm
                                                 pure $ delayMeta r envb (type def) tm
                                     let gdef = { definition := Guess tm' envb newcs } def
                                     ignore $ addDef (Resolved hid) gdef
                                     pure False
               Guess tm envb constrs =>
                 do let umode = case smode of
                                     MatchArgs => inMatch
                                     _ => mode
                    cs' <- traverse (retry umode) constrs
                    let csAll = unionAll cs'
                    case constraints csAll of
                         -- All constraints resolved, so turn into a
                         -- proper definition and remove it from the
                         -- hole list
                         [] => do let gdef = { definition := Function reducePI tm tm Nothing } def
                                  logTerm "unify.retry" 5 ("Resolved " ++ show hname) tm
                                  ignore $ addDef (Resolved hid) gdef
                                  removeGuess hid
                                  pure (holesSolved csAll)
                         newcs => do let gdef = { definition := Guess tm envb newcs } def
                                     ignore $ addDef (Resolved hid) gdef
                                     pure False
               _ => pure False

export
solveConstraints : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   UnifyInfo -> (smode : SolveMode) -> Core ()
solveConstraints umode smode
    = do ust <- get UST
         progress <- traverse (retryGuess umode smode) (toList (guesses ust))
         when (any id progress) $
               solveConstraints umode Normal

export
solveConstraintsAfter : {auto c : Ref Ctxt Defs} ->
                        {auto u : Ref UST UState} ->
                        Int -> UnifyInfo -> (smode : SolveMode) -> Core ()
solveConstraintsAfter start umode smode
    = do ust <- get UST
         progress <- traverse (retryGuess umode smode)
                              (filter afterStart (toList (guesses ust)))
         when (any id progress) $
               solveConstraintsAfter start umode Normal
  where
    afterStart : (Int, a) -> Bool
    afterStart (x, _) = x >= start

-- Replace any 'BySearch' with 'Hole', so that we don't keep searching
-- fruitlessly while elaborating the rest of a source file
export
giveUpConstraints : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    Core ()
giveUpConstraints
    = do ust <- get UST
         traverse_ constraintToHole (toList (guesses ust))
  where
    constraintToHole : (Int, (FC, Name)) -> Core ()
    constraintToHole (hid, (_, _))
        = do defs <- get Ctxt
             case !(lookupDefExact (Resolved hid) (gamma defs)) of
                  Just (BySearch {}) =>
                         updateDef (Resolved hid) (const (Just (Hole 0 (holeInit False))))
                  Just (Guess {}) =>
                         updateDef (Resolved hid) (const (Just (Hole 0 (holeInit False))))
                  _ => pure ()

-- Check whether any of the given hole references have the same solution
-- (up to conversion)
export
checkArgsSame : {auto u : Ref UST UState} ->
                {auto c : Ref Ctxt Defs} ->
                List Int -> Core Bool
checkArgsSame [] = pure False
checkArgsSame (x :: xs)
    = do defs <- get Ctxt
         Just (Function _ def _ _) <-
                    lookupDefExact (Resolved x) (gamma defs)
              | _ => checkArgsSame xs
         s <- anySame def xs
         if s
            then pure True
            else checkArgsSame xs
  where
    anySame : ClosedTerm -> List Int -> Core Bool
    anySame tm [] = pure False
    anySame tm (t :: ts)
        = do defs <- get Ctxt
             Just (Function _ def _ _) <-
                        lookupDefExact (Resolved t) (gamma defs)
                  | _ => anySame tm ts
             if !(convert Env.empty tm def)
                then pure True
                else anySame tm ts

export
checkDots : {auto u : Ref UST UState} ->
            {auto c : Ref Ctxt Defs} ->
            Core ()
checkDots
    = do ust <- get UST
         hs <- getCurrentHoles
         traverse_ checkConstraint (reverse (dotConstraints ust))
         hs <- getCurrentHoles
         update UST { dotConstraints := [] }
  where
    getHoleName : Term [<] -> Core (Maybe Name)
    getHoleName tm
        = do defs <- get Ctxt
             VMeta _ n' i _ _ _ <- expand !(nf Env.empty tm)
                 | _ => pure Nothing
             pure (Just n')

    checkConstraint : (Name, DotReason, Constraint) -> Core ()
    checkConstraint (n, reason, MkConstraint fc _ env xold yold)
        = do defs <- get Ctxt
             x <- nf env xold
             y <- nf env yold
             logNF "unify.constraint" 10 "Dot" env y
             logNF "unify.constraint" 10 "  =" env x
             -- A dot is okay if the constraint is solvable *without solving
             -- any additional holes*
             ust <- get UST
             handleUnify
               (do defs <- get Ctxt
                   -- get the hole name that 'n' is currently resolved to,
                   -- if indeed it is still a hole
                   (i, _) <- getPosition n (gamma defs)
                   oldholen <- getHoleName (Meta fc n i [])

                   -- Check that what was given (x) matches what was
                   -- solved by unification (y).
                   -- In 'InMatch' mode, only metavariables in 'x' can
                   -- be solved, so everything in the dotted metavariable
                   -- must be complete.
                   cs <- unify inMatch fc env x y
                   defs <- get Ctxt

                   -- If the name standing for the dot wasn't solved
                   -- earlier, but is now (even with another metavariable)
                   -- this is bad (it most likely means there's a non-linear
                   -- variable)
                   dotSolved <-
                      maybe (pure False)
                            (\n => do Just ndef <- lookupDefExact n (gamma defs)
                                           | Nothing => undefinedName fc n
                                      pure $ case ndef of
                                           Hole {} => False
                                           _ => True)
                            oldholen

                   -- If any of the things we solved have the same definition,
                   -- we've sneaked a non-linear pattern variable in
                   argsSame <- checkArgsSame (namesSolved cs)
                   when (not (isNil (constraints cs))
                            || dotSolved || argsSame) $
                      throw (InternalError "Dot pattern match fail"))
               (\err =>
                    case err of
                         InternalError _ =>
                           do defs <- get Ctxt
                              Just dty <- lookupTyExact n (gamma defs)
                                   | Nothing => undefinedName fc n
                              logTermNF "unify.constraint" 5 "Dot type" Env.empty dty
                              -- Clear constraints so we don't report again
                              -- later
                              put UST ({ dotConstraints := [] } ust)
                              throw (BadDotPattern fc env reason
                                      !(quote env x)
                                      !(quote env y))
                         _ => do put UST ({ dotConstraints := [] } ust)
                                 throw err)
    checkConstraint _ = pure ()
