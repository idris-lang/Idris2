module Core.Env

import Core.TT
import Core.Name.CompatibleVars
import Data.List
import Data.SnocList

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.HasLength

%default total

-- Environment containing types and values of local variables
public export
data Env : (tm : SnocList Name -> Type) -> SnocList Name -> Type where
     Lin : Env tm [<]
     (:<) : Env tm vars -> Binder (tm vars) -> Env tm (vars :< x)

%name Env rho

export
extend : (x : Name) -> Env tm vars -> Binder (tm vars) ->  Env tm (vars :< x)
extend x = (:<) {x}

export
(++) : {ns : _} -> Env Term ns -> Env Term vars -> Env Term (vars ++ ns)
(++) (bs :< b) e = extend _ (bs ++ e) (map embed b)
(++) [<] e = e

export
length : Env tm xs -> Nat
length [<] = 0
length (xs :< _) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [<] = 0
lengthNoLet (xs :< Let _ _ _ _) = lengthNoLet xs
lengthNoLet (xs :< _) = S (lengthNoLet xs)

export
lengthExplicitPi : Env tm xs -> Nat
lengthExplicitPi [<] = 0
lengthExplicitPi (rho :< Pi _ _ Explicit _) = S (lengthExplicitPi rho)
lengthExplicitPi (rho :< _) = lengthExplicitPi rho

export
namesNoLet : {xs : _} -> Env tm xs -> SnocList Name
namesNoLet [<] = [<]
namesNoLet (xs :< Let _ _ _ _) = namesNoLet xs
namesNoLet {xs = _ :< x} (env :< _) = namesNoLet env :< x

public export
data IsDefined : Name -> SnocList Name -> Type where
  MkIsDefined : {idx : Nat} -> RigCount -> (0 p : IsVar n idx vars) ->
                IsDefined n vars

export
defined : {vars : _} ->
          (n : Name) -> Env Term vars ->
          Maybe (IsDefined n vars)
defined n [<] = Nothing
defined {vars = xs :< x} n (env :< b)
    = case nameEq n x of
           Nothing => do MkIsDefined rig prf <- defined n env
                         pure (MkIsDefined rig (Later prf))
           Just Refl => Just (MkIsDefined (multiplicity b) First)

-- Bind additional pattern variables in an LHS, when checking an LHS in an
-- outer environment
export
bindEnv : {vars : _} -> FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv loc [<] tm = tm
bindEnv loc (env :< b) tm
    = bindEnv loc env (Bind loc _ (PVar (binderLoc b)
                                        (multiplicity b)
                                        Explicit
                                        (binderType b)) tm)

public export
revOnto : (xs, vs : SnocList a) -> reverseOnto xs vs = xs ++ reverse vs
revOnto xs [<] = Refl
revOnto xs (vs :< v)
    = rewrite revOnto (xs :< v) vs in
        rewrite revOnto [<v] vs in
          rewrite appendAssociative xs [<v] (reverse vs) in Refl

public export
revNs : (vs, ns : SnocList a) -> reverse vs ++ reverse ns = reverse (ns ++ vs)
revNs [<] ns = rewrite appendLinLeftNeutral (reverse ns) in Refl
revNs (vs :< v) ns
    = rewrite revOnto [<v] vs in
        rewrite revOnto [<v] (ns ++ vs) in
          rewrite sym $ revNs vs ns in
            rewrite appendAssociative [<v] (reverse vs) (reverse ns) in Refl

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : SnocList Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (reverseOnto vars ns))
getBinderUnder {idx = Z} {vars = vs :< v} ns First (env :< b)
    = rewrite revOnto (vs :< x) ns in
        rewrite sym $ appendAssociative vs [<v] (reverse ns) in
                map (weakenNs (sucR (reverse (mkSizeOf ns)))) b
getBinderUnder {idx = S k} {vars = vs :< v} ns (Later lp) (env :< b)
    = getBinderUnder (ns :< v) lp env


export
getBinder : Weaken tm =>
            {vars : _} -> {idx : Nat} ->
            (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [<] el env

-- For getBinderLoc, we are not reusing getBinder because there is no need to
-- needlessly weaken stuff;
export
getBinderLoc : {vars : _} -> {idx : Nat} -> (0 p : IsVar x idx vars) -> Env tm vars -> FC
getBinderLoc {idx = Z}   First     (_ :< b)   = binderLoc b
getBinderLoc {idx = S k} (Later p) (env :< _) = getBinderLoc p env

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : {vars : _} ->
                  FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnvType fc [<] tm = tm
abstractEnvType fc (env :< Let fc' c val ty) tm
    = abstractEnvType fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnvType fc (env :< Pi fc' c e ty) tm
    = abstractEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractEnvType fc (env :< b) tm
    = let bnd = Pi (binderLoc b) (multiplicity b) Explicit (binderType b)
       in abstractEnvType fc env (Bind fc _ bnd tm)

-- As above, for the corresponding term
export
abstractEnv : {vars : _} ->
              FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnv fc [<] tm = tm
abstractEnv fc (env :< Let fc' c val ty) tm
    = abstractEnv fc env (Bind fc _ (Let fc' c val ty) tm)
abstractEnv fc (env :< b) tm
    = let bnd = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)
      in abstractEnv fc env (Bind fc _ bnd tm)

-- As above, but abstract over all binders including lets
export
abstractFullEnvType : {vars : _} ->
                      FC -> Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractFullEnvType fc [<] tm = tm
abstractFullEnvType fc (env :< Pi fc' c e ty) tm
    = abstractFullEnvType fc env (Bind fc _ (Pi fc' c e ty) tm)
abstractFullEnvType fc (env :< b) tm
    = let bnd = Pi fc (multiplicity b) Explicit (binderType b)
      in abstractFullEnvType fc env (Bind fc _ bnd tm)

export
letToLam : Env Term vars -> Env Term vars
letToLam [<] = [<]
letToLam (env :< Let fc c val ty) = letToLam env :< Lam fc c Explicit ty
letToLam (env :< b) = letToLam env :< b

mutual
  -- Quicker, if less safe, to store variables as a Nat, for quick comparison
  findUsed : {vars : _} ->
             Env Term vars -> SnocList Nat -> Term vars -> SnocList Nat
  findUsed env used (Local fc r idx p)
      = if elemBy eqNat idx used
           then used
           else assert_total (findUsedInBinder env (used :< idx)
                                               (getBinder p env))
    where
      eqNat : Nat -> Nat -> Bool
      eqNat i j = natToInteger i == natToInteger j
  findUsed env used (Meta _ _ _ args)
      = findUsedArgs env used args
    where
      findUsedArgs : Env Term vars -> SnocList Nat -> List (Term vars) -> SnocList Nat
      findUsedArgs env u [] = u
      findUsedArgs env u (a :: as)
          = findUsedArgs env (findUsed env u a) as
  findUsed env used (Bind fc x b tm)
      = assert_total $
          dropS (findUsed (env :< b)
                          (map S (findUsedInBinder env used b))
                          tm)
    where
      dropS : SnocList Nat -> SnocList Nat
      dropS [<] = [<]
      dropS (xs :< Z) = dropS xs
      dropS (xs :< S p) = dropS xs :< p
  findUsed env used (App fc fn arg)
      = findUsed env (findUsed env used fn) arg
  findUsed env used (As fc s a p)
      = findUsed env (findUsed env used a) p
  findUsed env used (TDelayed fc r tm)
      = findUsed env used tm
  findUsed env used (TDelay fc r ty tm)
      = findUsed env (findUsed env used ty) tm
  findUsed env used (TForce fc r tm)
      = findUsed env used tm
  findUsed env used _ = used

  findUsedInBinder : {vars : _} ->
                     Env Term vars -> SnocList Nat ->
                     Binder (Term vars) -> SnocList Nat
  findUsedInBinder env used (Let _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used (PLet _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used b = findUsed env used (binderType b)

toVar : (vars : SnocList Name) -> Nat -> Maybe (Var vars)
toVar (vs :< v) Z = Just (MkVar First)
toVar (vs :< v) (S k)
   = do MkVar prf <- toVar vs k
        Just (MkVar (Later prf))
toVar _ _ = Nothing

export
findUsedLocs : {vars : _} ->
               Env Term vars -> Term vars -> SnocList (Var vars)
findUsedLocs env tm
    = mapMaybe (toVar _) (findUsed env [<] tm)

isUsed : Nat -> SnocList (Var vars) -> Bool
isUsed n [<] = False
isUsed n (vs :< v) = n == varIdx v || isUsed n vs

mkShrinkSub : {n : _} ->
              (vars : _) -> SnocList (Var (vars :< n)) ->
              (newvars ** Thin newvars (vars :< n))
mkShrinkSub [<] els
    = if isUsed 0 els
         then (_ ** Keep Refl)
         else (_ ** Drop Refl)
mkShrinkSub (xs :< x) els
    = let (_ ** subRest) = mkShrinkSub xs (dropFirst els) in
      if isUsed 0 els
        then (_ ** Keep subRest)
        else (_ ** Drop subRest)

mkShrink : {vars : _} ->
           SnocList (Var vars) ->
           (newvars ** Thin newvars vars)
mkShrink {vars = [<]} xs = (_ ** Refl)
mkShrink {vars = vs :< v} xs = mkShrinkSub _ xs

-- Find the smallest subset of the environment which is needed to type check
-- the given term
export
findSubEnv : {vars : _} ->
             Env Term vars -> Term vars ->
             (vars' : SnocList Name ** Thin vars' vars)
findSubEnv env tm = mkShrink (findUsedLocs env tm)

export
shrinkEnv : Env Term vars -> Thin newvars vars -> Maybe (Env Term newvars)
shrinkEnv env Refl = Just env
shrinkEnv (env :< b) (Drop p) = shrinkEnv env p
shrinkEnv (env :< b) (Keep p)
    = do env' <- shrinkEnv env p
         b' <- assert_total (shrinkBinder b p)
         pure (env' :< b')

export
mkEnvOnto : FC -> (xs : SnocList Name) -> Env Term ys -> Env Term (ys ++ xs)
mkEnvOnto fc [<] vs = vs
mkEnvOnto fc (ns :< n) vs
   = mkEnvOnto fc ns vs :< PVar fc top Explicit (Erased fc Placeholder)

-- Make a dummy environment, if we genuinely don't care about the values
-- and types of the contents.
-- We use this when building and comparing case trees.
export
mkEnv : FC -> (vs : SnocList Name) -> Env Term vs
mkEnv fc [<] = [<]
mkEnv fc (ns :< n) = mkEnv fc ns :< PVar fc top Explicit (Erased fc Placeholder)

-- Update an environment so that all names are guaranteed unique. In the
-- case of a clash, the most recently bound is left unchanged.
export
uniqifyEnv : {vars : _} ->
             Env Term vars ->
             (vars' ** (Env Term vars', CompatibleVars vars vars'))
uniqifyEnv env = uenv [<] env
  where
    next : Name -> Name
    next (MN n i) = MN n (i + 1)
    next (UN n) = MN (displayUserName n) 0
    next (NS ns n) = NS ns (next n)
    next n = MN (show n) 0

    uniqueLocal : SnocList Name -> Name -> Name
    uniqueLocal vs n
       = if n `elem` vs
                 -- we'll find a new name eventualy since the list of names
                 -- is empty, and next generates something new. But next has
                 -- to be correct... an exercise for someone: this could
                 -- probebly be done without an assertion by making a stream of
                 -- possible names...
            then assert_total (uniqueLocal vs (next n))
            else n

    uenv : {vars : _} ->
           SnocList Name -> Env Term vars ->
           (vars' ** (Env Term vars', CompatibleVars vars vars'))
    uenv used [<] = ([<] ** ([<], Pre))
    uenv used {vars = vs :< v} (bs :< b)
        = if v `elem` used
             then let v' = uniqueLocal used v
                      (vs' ** (env', compat)) = uenv (used :< v') bs
                      b' = map (compatNs compat) b in
                  (vs' :< v' ** (env' :< b', Ext compat))
             else let (vs' ** (env', compat)) = uenv (used :< v) bs
                      b' = map (compatNs compat) b in
                  (vs' :< v ** (env' :< b', Ext compat))

export
allVars : {vars : _} -> Env Term vars -> List (Var vars)
allVars [<] = []
allVars (vs :< v) = MkVar First :: map weaken (allVars vs)

export
allVarsNoLet : {vars : _} -> Env Term vars -> List (Var vars)
allVarsNoLet [<] = []
allVarsNoLet (vs :< Let _ _ _ _) = map weaken (allVars vs)
allVarsNoLet (vs :< v) = MkVar First :: map weaken (allVars vs)

export
close : FC -> String -> Env Term vars -> Term vars -> ClosedTerm
close fc nm env tm
  = let (s, env) = mkSubstEnv 0 env in
    substs s env (rewrite appendLinLeftNeutral vars in tm)

  where
    mkSubstEnv : Int -> Env Term vs -> (SizeOf vs, SubstEnv vs [<])
    mkSubstEnv i [<] = (zero, [<])
    mkSubstEnv i (vs :< v)
       = let (s, env) = mkSubstEnv (i + 1) vs in
         (suc s, env :< Ref fc Bound (MN nm i))
