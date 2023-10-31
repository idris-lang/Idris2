module Core.TT.Subst

import Core.FC
import Core.Name
import Core.Name.Scoped
import Core.TT.Binder
import Core.TT.Term
import Core.TT.Var

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
  SizeOf local -> Subst target outer ->
  FC -> Maybe Bool -> Var ((outer ++ target) ++ local) ->
  Term (outer ++ local)
substLocal local env fc r var = case locateVar local var of
  Right (MkVar p) => Local fc r _ (embedIsVar p)
  Left v => weakenNs local $ lookup fc r v env


||| What it means for a type to have a substitution action
||| Note the generalised type working under an arbitrary scope
||| of locally bound variables.
public export
0 Substable : (tm : Scoped) -> Type
Substable tm = {0 local, target, outer : Scope} ->
  SizeOf local -> Subst target outer ->
  tm ((outer ++ target) ++ local) -> tm (outer ++ local)

mutual

  substBinder : Substable (Binder . Term)
  substBinder local env b = assert_total $ map (substTerm local env) b

  substTerms : Substable (List . Term)
  substTerms local env xs = assert_total $ map (substTerm local env) xs

  export
  substTerm : Substable Term
  substTerm local env (Local fc r _ prf)
      = substLocal local env fc r (MkVar prf)
  substTerm local env (Ref fc x name) = Ref fc x name
  substTerm local env (Meta fc n i xs)
      = Meta fc n i (substTerms local env xs)
  substTerm local env (Bind fc x b scope)
      = Bind fc x (substBinder local env b)
                  (substTerm (suc local) env scope)
  substTerm local env (App fc fn arg)
      = App fc (substTerm local env fn) (substTerm local env arg)
  substTerm local env (As fc s as pat)
      = As fc s (substTerm local env as) (substTerm local env pat)
  substTerm local env (TDelayed fc x y) = TDelayed fc x (substTerm local env y)
  substTerm local env (TDelay fc x t y)
      = TDelay fc x (substTerm local env t) (substTerm local env y)
  substTerm local env (TForce fc r x) = TForce fc r (substTerm local env x)
  substTerm local env (PrimVal fc c) = PrimVal fc c
  substTerm local env (Erased fc Impossible) = Erased fc Impossible
  substTerm local env (Erased fc Placeholder) = Erased fc Placeholder
  substTerm local env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm local env t))
  substTerm local env (TType fc u) = TType fc u


||| Parallel substitution
export
substs : Subst target outer -> Term (outer ++ target) -> Term outer
substs env tm = substTerm zero env tm

||| Substitution for the most local variable
export
subst : Term vars -> Term (vars :< x) -> Term vars
subst val tm = substs [<val] tm


public export
0 SubstRef : Scoped -> Type
SubstRef tm = {0 vars, local : Scope} -> SizeOf local -> Name -> Term vars ->
    tm (vars ++ local) -> tm (vars ++ local)

mutual

  substRefBinder : SubstRef (Binder . Term)
  substRefBinder s x new b = assert_total $ map (substRefTerm s x new) b

  substRefTerms : SubstRef (List . Term)
  substRefTerms s x new xs = assert_total $ map (substRefTerm s x new) xs

  ||| Replace a global name with a term
  export
  substRefTerm : SubstRef Term
  substRefTerm s x new (Ref fc nt name)
      = case nameEq x name of
             Nothing => Ref fc nt name
             Just Refl => weakenNs s new
  substRefTerm s x new (Meta fc n i xs)
      = Meta fc n i (substRefTerms s x new xs)
  -- ASSUMPTION: When we substitute under binders, the name has always been
  -- resolved to a Local, so no need to check that x isn't shadowing
  substRefTerm s x new (Bind fc y b scope)
      = Bind fc y (substRefBinder s x new b) (substRefTerm (suc s) x new scope)
  substRefTerm s x new (App fc fn arg)
      = App fc (substRefTerm s x new fn) (substRefTerm s x new arg)
  substRefTerm s x new (As fc use as pat)
      = As fc use as (substRefTerm s x new pat)
  substRefTerm s x new (TDelayed fc y z)
      = TDelayed fc y (substRefTerm s x new z)
  substRefTerm s x new (TDelay fc y t z)
      = TDelay fc y (substRefTerm s x new t) (substRefTerm s x new z)
  substRefTerm s x new (TForce fc r y)
      = TForce fc r (substRefTerm s x new y)
  substRefTerm s x new tm = tm

export
substRef : Name -> Term vars -> Term vars -> Term vars
substRef = substRefTerm zero
