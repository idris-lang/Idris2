module Core.Env

import Data.SnocList
import Core.TT

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf

%default total

||| Environment containing types and values of local variables
public export
data Env : Scoped -> Scoped where
  Lin : Env tm [<]
  (:<) : Env tm vars -> Binder (tm vars) -> Env tm (vars :< x)

%name Env rho

export
extend : (x : Name) -> Binder (tm vars) -> Env tm vars -> Env tm (vars :< x)
extend x = flip ((:<) {x})

export
(++) : FreelyEmbeddable tm => Env tm ns -> Env tm vars -> Env tm (ns ++ vars)
vs ++ [<] = vs
vs ++ (rho :< bd) = (vs ++ rho) :< map embed bd

export
length : Env tm xs -> Nat
length [<] = 0
length (xs :< _) = S (length xs)

export
lengthNoLet : Env tm xs -> Nat
lengthNoLet [<] = 0
lengthNoLet (xs :< Let _  _ _ _) = lengthNoLet xs
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
data IsDefined : Name -> Scoped where
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

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : List Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (vars <>< ns))
getBinderUnder {idx = Z} {vars = vs :< v} ns First (env :< b)
    = map (rewrite fishAsSnocAppend vs (v :: ns) in weakenNs (suc zero <>< mkSizeOf ns)) b
getBinderUnder {idx = S k} {vars = vs :< v} ns (Later lp) (env :< b)
    = getBinderUnder (v :: ns) lp env

export
getBinder : Weaken tm =>
            {vars : _} -> {idx : Nat} ->
            (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env

-- For getBinderLoc, we are not reusing getBinder because there is no need to
-- needlessly weaken stuff;
export
getBinderLoc : {vars : _} -> {idx : Nat} -> (0 p : IsVar x idx vars) -> Env tm vars -> FC
getBinderLoc {idx = Z}  First (_ :< b)   = binderLoc b
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

0 FindUsed : Scoped -> Type
FindUsed tm
  = {vars : _} ->
    Env Term vars -> -- binders found on the way
    List (Var vars) -> -- accumulator
    tm vars -> List (Var vars)

mutual
  -- WAS: Quicker, if less safe, to store variables as a Nat, for quick comparison
  -- NOW: Actually using `Var` which AFAIK is just a Nat at runtime anyway?!
  -- Also: why are we using a List if it's performance critical?
  findUsed : FindUsed Term
  findUsed env used (Local fc r idx p)
      = let var = MkVar p in
        if var `elem` used
           then used
           else assert_total (findUsedInBinder env (var :: used)
                                               (getBinder p env))
  findUsed env used (Meta _ _ _ args)
      = findUsedTerms env used args
  findUsed env used (Bind fc x b tm)
      = assert_total
      $ dropFirst
      $ findUsed (env :< b)
          (map later (findUsedInBinder env used b))
          tm
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

  findUsedTerms : FindUsed (List . Term)
  findUsedTerms env u [] = u
  findUsedTerms env u (a :: as) = findUsedTerms env (findUsed env u a) as

  findUsedInBinder : FindUsed (Binder . Term)
  findUsedInBinder env used (Let _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used (PLet _ _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used b = findUsed env used (binderType b)

export
findUsedLocs : {vars : _} ->
               Env Term vars -> Term vars -> List (Var vars)
findUsedLocs env tm = findUsed env [] tm

-- Find the smallest subset of the environment which is needed to type check
-- the given term
export
findSubEnv : {vars : _} ->
             Env Term vars -> Term vars ->
             (vars' : Scope ** Thin vars' vars)
findSubEnv env tm = thinFromVars _ (findUsedLocs env tm)

export
shrinkEnv : Shrinkable (Env Term)
shrinkEnv env Refl = Just env
shrinkEnv (env :< b) (Drop p) = shrinkEnv env p
shrinkEnv (env :< b) (Keep p)
    = do env' <- shrinkEnv env p
         b' <- assert_total (shrinkBinder b p)
         pure (env' :< b')

export
mkEnvOnto : FC -> (local : Scope) -> Env Term ys -> Env Term (ys ++ local)
mkEnvOnto fc [<] vs = vs
mkEnvOnto fc (ns :< n) vs
   = mkEnvOnto fc ns vs
   :< PVar fc top Explicit (Erased fc Placeholder)

-- Make a dummy environment, if we genuinely don't care about the values
-- and types of the contents.
-- We use this when building and comparing case trees.
export
mkEnv : FC -> (vs : Scope) -> Env Term vs
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
    uenv : {vars : _} ->
           Scope -> Env Term vars ->
           (vars' ** (Env Term vars', CompatibleVars vars vars'))
    uenv used [<] = ([<] ** ([<], Pre))
    uenv used {vars = vs :< v} (bs :< b)
        = if v `elem` used
             then let v' = uniqueLocal used v
                      (vs' ** (env', ren)) = uenv (used :< v') bs
                      b' = map (compatNs ren) b in
                  (vs' :< v' ** (env' :< b', Ext ren))
             else let (vs' ** (env', ren)) = uenv (used :< v) bs
                      b' = map (compatNs ren) b in
                  (vs' :< v ** (env' :< b', Ext ren))

export
allVars : Env Term vars -> List (Var vars)
allVars = go zero where

   go : SizeOf inner -> Env Term outer -> List (Var (outer <>< inner))
   go s [<] = []
   go s (vs :< v) = fishyVar s :: go (suc s) vs

export
allVarsNoLet : {vars : _} -> Env Term vars -> List (Var vars)
allVarsNoLet = go zero where

   go : SizeOf inner -> Env Term outer -> List (Var (outer <>< inner))
   go s [<] = []
   go s (vs :< Let _ _ _ _) = go (suc s) vs
   go s (vs :< v) = fishyVar s :: go (suc s) vs
