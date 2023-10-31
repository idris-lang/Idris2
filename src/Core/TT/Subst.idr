module Core.TT.Subst

import Core.FC
import Core.Name
import Core.Name.Scoped
import Core.TT.Var
import Core.TT.Term

import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default total

public export
data Subst : SnocList Name -> Scoped where
  Lin : Subst [<] vars
  (:<) : Subst ds vars -> Term vars -> Subst (ds :< d) vars

lookup :
  {0 outer, target : _} ->
  FC -> Maybe Bool ->
  Var (outer ++ target) -> Subst target outer ->
  Term outer
lookup fc r (MkVar p) [<] = Local fc r _ p
lookup fc r (MkVar First) (_ :< t) = t
lookup fc r (MkVar (Later idx)) (env :< _) = lookup fc r (MkVar idx) env

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
substLocal :
  FC -> Maybe Bool ->
  SizeOf local ->
  Var ((outer ++ target) ++ local) ->
  Subst target outer ->
  Term (outer ++ local)
substLocal fc r local var env = case locateVar local var of
  Right (MkVar p) => Local fc r _ (embedIsVar p)
  Left v => weakenNs local $ lookup fc r v env

{-

  substSubst : SizeOf outer ->
             SubstSubst dropped vars ->
             Term (outer ++ (dropped ++ vars)) ->
             Term (outer ++ vars)
  substSubst outer env (Local fc r _ prf)
      = find fc r outer (MkVar prf) env
  substSubst outer env (Ref fc x name) = Ref fc x name
  substSubst outer env (Meta fc n i xs)
      = Meta fc n i (map (substSubst outer env) xs)
  substSubst outer env (Bind fc x b scope)
      = Bind fc x (map (substSubst outer env) b)
                  (substSubst (suc outer) env scope)
  substSubst outer env (App fc fn arg)
      = App fc (substSubst outer env fn) (substSubst outer env arg)
  substSubst outer env (As fc s as pat)
      = As fc s (substSubst outer env as) (substSubst outer env pat)
  substSubst outer env (TDelayed fc x y) = TDelayed fc x (substSubst outer env y)
  substSubst outer env (TDelay fc x t y)
      = TDelay fc x (substSubst outer env t) (substSubst outer env y)
  substSubst outer env (TForce fc r x) = TForce fc r (substSubst outer env x)
  substSubst outer env (PrimVal fc c) = PrimVal fc c
  substSubst outer env (Erased fc Impossible) = Erased fc Impossible
  substSubst outer env (Erased fc Placeholder) = Erased fc Placeholder
  substSubst outer env (Erased fc (Dotted t)) = Erased fc (Dotted (substSubst outer env t))
  substSubst outer env (TType fc u) = TType fc u

  export
  substs : SubstSubst dropped vars -> Term (dropped ++ vars) -> Term vars
  substs env tm = substSubst zero env tm

  export
  subst : Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substs [val] tm

-- Replace an explicit name with a term
export
substName : Name -> Term vars -> Term vars -> Term vars
substName x new (Ref fc nt name)
    = case nameEq x name of
           Nothing => Ref fc nt name
           Just Refl => new
substName x new (Meta fc n i xs)
    = Meta fc n i (map (substName x new) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind fc y b scope)
    = Bind fc y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App fc fn arg)
    = App fc (substName x new fn) (substName x new arg)
substName x new (As fc s as pat)
    = As fc s as (substName x new pat)
substName x new (TDelayed fc y z)
    = TDelayed fc y (substName x new z)
substName x new (TDelay fc y t z)
    = TDelay fc y (substName x new t) (substName x new z)
substName x new (TForce fc r y)
    = TForce fc r (substName x new y)
substName x new tm = tm
