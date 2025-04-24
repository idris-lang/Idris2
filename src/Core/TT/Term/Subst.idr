module Core.TT.Term.Subst

import Algebra
import Core.Name.Scoped

import Core.TT.Binder
import Core.TT.Subst
import Core.TT.Term
import Core.TT.Var

import Data.Vect
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf

%default total

public export
SubstEnv : Scope -> Scoped
SubstEnv = Subst Term

single : Term vars -> SubstEnv [<x] vars
single n = [<n]

findDropVar : Var (Scope.addInner outer dropped) ->
              SubstEnv dropped outer ->
              Maybe (Var outer)
findDropVar (MkVar var) [<] = Just (MkVar var)
findDropVar (MkVar First) (env :< tm) = Nothing
findDropVar (MkVar (Later p)) (env :< tm)
    = findDropVar (MkVar p) env

findVar : SizeOf inner ->
          Var (Scope.addInner (Scope.addInner outer dropped) inner) ->
          SubstEnv dropped outer ->
          Maybe (Var (Scope.addInner outer inner))
findVar inn var env = case sizedView inn of
  Z       => findDropVar var env
  S inn => case var of
    MkVar First     => Just (MkVar First)
    MkVar (Later p) => map weaken (findVar inn (MkVar p) env)

substTerm : Substitutable Term Term
substTerms : Substitutable Term (List . Term)
substVect : forall a. Substitutable Term (Vect a . Term)
substBinder : Substitutable Term (Binder . Term)
substTaggedTerms : forall a. Substitutable Term (List . (a,) . Term)
substAlt : Substitutable Term CaseAlt
substCaseScope : Substitutable Term CaseScope

substTerm drp inn env (Local fc r _ prf)
    = find (\ (MkVar p) => Local fc r _ p) drp inn (MkVar prf) env
substTerm drp inn env (Ref fc x name) = Ref fc x name
substTerm drp inn env (Meta fc n i xs)
    = Meta fc n i (substTaggedTerms drp inn env xs)
substTerm drp inn env (Bind fc x b scope)
    = Bind fc x (substBinder drp inn env b)
                (substTerm drp (suc inn) env scope)
substTerm drp inn env (App fc fn c arg)
    = App fc (substTerm drp inn env fn) c (substTerm drp inn env arg)
substTerm drp inn env (As fc s as pat)
    = As fc s (substTerm drp inn env as) (substTerm drp inn env pat)
substTerm drp inn env (Case fc t c sc scty alts)
    = Case fc t c (substTerm drp inn env sc)
                  (substTerm drp inn env scty)
                  (map (assert_total $ substAlt drp inn env) alts)
substTerm drp inn env (TDelayed fc x y) = TDelayed fc x (substTerm drp inn env y)
substTerm drp inn env (TDelay fc x t y)
    = TDelay fc x (substTerm drp inn env t) (substTerm drp inn env y)
substTerm drp inn env (TForce fc r x) = TForce fc r (substTerm drp inn env x)
substTerm drp inn env (PrimVal fc c) = PrimVal fc c
substTerm drp inn env (PrimOp fc x args)
    = PrimOp fc x (substVect drp inn env args)
substTerm drp inn env (Erased fc Impossible) = Erased fc Impossible
substTerm drp inn env (Erased fc Placeholder) = Erased fc Placeholder
substTerm drp inn env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm drp inn env t))
substTerm drp inn env (Unmatched fc u) = Unmatched fc u
substTerm drp inn env (TType fc u) = TType fc u

substTerms drp inn env xs
  = assert_total $ map (substTerm drp inn env) xs

substVect drp inn env xs
  = assert_total $ map (substTerm drp inn env) xs

substBinder drp inn env b
  = assert_total $ map (substTerm drp inn env) b

substTaggedTerms drp inn env b
  = assert_total $ map @{Compose} (substTerm drp inn env) b

substCaseScope drp inn env (RHS fs tm)
  = RHS (substForced fs) (substTerm drp inn env tm)
  where
    -- If we substitute in the vars, the equality is no longer useful
    substForced : List (Var (Scope.addInner (Scope.addInner outer dropped) inner), Term (Scope.addInner (Scope.addInner outer dropped) inner)) ->
                  List (Var (Scope.addInner outer inner), Term (Scope.addInner outer inner))
    substForced [] = []
    substForced ((v, tm) :: fs)
        = case findVar inn v env of
              Nothing => substForced fs
              Just v' => ((v', substTerm drp inn env tm) :: substForced fs)

substCaseScope drp inn env (Arg c x sc) = Arg c x (substCaseScope drp (suc inn) env sc)

substAlt drp inn env (ConCase fc n t sc) = ConCase fc n t (substCaseScope drp inn env sc)
substAlt drp inn env (DelayCase fc ty arg sc) = DelayCase fc ty arg (substTerm drp (suc (suc inn)) env sc)
substAlt drp inn env (ConstCase fc c sc) = ConstCase fc c (substTerm drp inn env sc)
substAlt drp inn env (DefaultCase fc sc) = DefaultCase fc (substTerm drp inn env sc)

export
substs : SizeOf dropped -> SubstEnv dropped vars -> Term (Scope.addInner vars dropped) -> Term vars
substs dropped env tm = substTerm dropped zero env tm

export
subst : Term vars -> Term (Scope.bind vars x) -> Term vars
subst val tm = substs (suc zero) (Subst.single val) tm
