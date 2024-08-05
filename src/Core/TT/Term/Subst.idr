module Core.TT.Term.Subst

import Core.Name
import Core.Name.Scoped
import Core.Name.ScopedList

import Core.TT.Binder
import Core.TT.Subst
import Core.TT.Term
import Core.TT.Var

%default total

public export
SubstEnv : Scope -> Scoped
SubstEnv = Subst Term

substTerm : Substitutable Term Term
substTerms : Substitutable Term (List . Term)
substBinder : Substitutable Term (Binder . Term)

substTerm outer dropped env (Local fc r _ prf)
    = find (\ (MkVar p) => Local fc r _ p) outer dropped (MkVar prf) env
substTerm outer dropped env (Ref fc x name) = Ref fc x name
substTerm outer dropped env (Meta fc n i xs)
    = Meta fc n i (substTerms outer dropped env xs)
substTerm outer dropped env (Bind fc x b scope)
    = Bind fc x (substBinder outer dropped env b)
                (substTerm (suc outer) dropped env scope)
substTerm outer dropped env (App fc fn arg)
    = App fc (substTerm outer dropped env fn) (substTerm outer dropped env arg)
substTerm outer dropped env (As fc s as pat)
    = As fc s (substTerm outer dropped env as) (substTerm outer dropped env pat)
substTerm outer dropped env (TDelayed fc x y) = TDelayed fc x (substTerm outer dropped env y)
substTerm outer dropped env (TDelay fc x t y)
    = TDelay fc x (substTerm outer dropped env t) (substTerm outer dropped env y)
substTerm outer dropped env (TForce fc r x) = TForce fc r (substTerm outer dropped env x)
substTerm outer dropped env (PrimVal fc c) = PrimVal fc c
substTerm outer dropped env (Erased fc Impossible) = Erased fc Impossible
substTerm outer dropped env (Erased fc Placeholder) = Erased fc Placeholder
substTerm outer dropped env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm outer dropped env t))
substTerm outer dropped env (TType fc u) = TType fc u

substTerms outer dropped env xs
  = assert_total $ map (substTerm outer dropped env) xs

substBinder outer dropped env b
  = assert_total $ map (substTerm outer dropped env) b

export
substs : SizeOf dropped -> SubstEnv dropped vars -> Term (dropped +%+ vars) -> Term vars
substs dropped env tm = substTerm zero dropped env tm

export
subst : Term vars -> Term (x :%: vars) -> Term vars
subst val tm = substs (suc zero) [val] tm
