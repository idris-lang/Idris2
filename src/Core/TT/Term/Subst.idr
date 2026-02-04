module Core.TT.Term.Subst

import Core.Name.Scoped

import Core.TT.Binder
import Core.TT.Subst
import Core.TT.Term
import Core.TT.Var

import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf

%default total

public export
SubstEnv : Scope -> Scoped
SubstEnv = Subst Term

single : Term vars -> SubstEnv [<x] vars
single n = [<n]

substTerm : Substitutable Term Term
substTerms : Substitutable Term (List . Term)
substBinder : Substitutable Term (Binder . Term)

substTerm drp inn env (Local fc r _ prf)
    = find (\ (MkVar p) => Local fc r _ p) drp inn (MkVar prf) env
substTerm drp inn env (Ref fc x name) = Ref fc x name
substTerm drp inn env (Meta fc n i xs)
    = Meta fc n i (substTerms drp inn env xs)
substTerm drp inn env (Bind fc x b scope)
    = Bind fc x (substBinder drp inn env b)
                (substTerm drp (suc inn) env scope)
substTerm drp inn env (App fc fn arg)
    = App fc (substTerm drp inn env fn) (substTerm drp inn env arg)
substTerm drp inn env (As fc s as pat)
    = As fc s (substTerm drp inn env as) (substTerm drp inn env pat)
substTerm drp inn env (TDelayed fc x y) = TDelayed fc x (substTerm drp inn env y)
substTerm drp inn env (TDelay fc x t y)
    = TDelay fc x (substTerm drp inn env t) (substTerm drp inn env y)
substTerm drp inn env (TForce fc r x) = TForce fc r (substTerm drp inn env x)
substTerm drp inn env (PrimVal fc c) = PrimVal fc c
substTerm drp inn env (Erased fc Impossible) = Erased fc Impossible
substTerm drp inn env (Erased fc Placeholder) = Erased fc Placeholder
substTerm drp inn env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm drp inn env t))
substTerm drp inn env (TType fc u) = TType fc u

substTerms drp inn env xs
  = assert_total $ map (substTerm drp inn env) xs

substBinder drp inn env b
  = assert_total $ map (substTerm drp inn env) b

export
substs : SizeOf dropped -> SubstEnv dropped vars -> Term (Scope.addInner vars dropped) -> Term vars
substs dropped env tm = substTerm dropped zero env tm

export
subst : Term vars -> Term (Scope.bind vars x) -> Term vars
subst val tm = substs (suc zero) (Subst.single val) tm
