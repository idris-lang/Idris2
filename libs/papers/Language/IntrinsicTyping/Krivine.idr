||| The content of this module is based on the paper
||| From Mathematics to Abstract Machine
||| A formal derivation of an executable Krivine machine
||| by Wouter Swierstra

module Language.IntrinsicTyping.Krivine

import Control.Function
import Data.DPair
import Data.List.Elem

%default total

------------------------------------------------------------------------
-- Section 2: Types & Terms

public export
data Ty = Base | Arr Ty Ty

%name Ty a, b

public export
Context : Type
Context = List Ty

public export
data Term : Context -> Ty -> Type where
  Lam : Term (a :: g) b -> Term g (Arr a b)
  App : {a : Ty} -> Term g (Arr a b) -> Term g a -> Term g b
  Var : Elem a g -> Term g a

data Closed : Ty -> Type
data Env : Context -> Type

public export
data Closed : Ty -> Type where
  Closure : Term g a -> Env g -> Closed a
  ClApp : {a : Ty} -> Closed (Arr a b) -> Closed a -> Closed b

public export
data Env : Context -> Type where
  Nil : Env []
  (::) : {a : Ty} -> Closed a -> Env g -> Env (a :: g)

namespace Value

  public export
  data IsValue : Closed g -> Type where
    Lam : IsValue (Closure (Lam b) env)

  public export
  data Value : Ty -> Type where
    Val : (c : Closed a) -> IsValue c -> Value a

------------------------------------------------------------------------
-- Section 3: Reduction

public export
data Redex : Ty -> Type where
  RVar : Elem a g -> Env g -> Redex a
  RApp : {a : Ty} -> Term g (Arr a b) -> Term g a -> Env g -> Redex b
  Beta : {a : Ty} -> Term (a :: g) b -> Env g -> Closed a -> Redex b

public export
redex : Redex a -> Closed a
redex (RVar v env) = Closure (Var v) env
redex (RApp f t env) = Closure (App f t) env
redex (Beta b env arg) = ClApp (Closure (Lam b) env) arg

public export
lookup : Env g -> Elem a g -> Closed a
lookup (v :: _) Here = v
lookup (_ :: vs) (There p) = lookup vs p

public export
contract : Redex a -> Closed a
contract (RVar v env) = lookup env v
contract (RApp f t env) = ClApp (Closure f env) (Closure t env)
contract (Beta b env arg) = Closure b (arg :: env)

namespace EvalContext

  public export
  data EvalContext : (inner, outer : Ty) -> Type where
    Nil : EvalContext inner inner
    (::) : Closed a -> EvalContext inner outer -> EvalContext (Arr a inner) outer

  public export
  snoc : EvalContext inner (Arr dom outer) -> Closed dom -> EvalContext inner outer
  snoc [] t = [t]
  snoc (hd :: ctx) t = hd :: snoc ctx t

  public export
  data SnocView : EvalContext inner outer -> Type where
    Lin : SnocView []
    (:<) : (ctx : EvalContext inner (Arr dom outer)) ->
           (t : Closed dom) ->
           SnocView (snoc ctx t)

  public export
  snocView : (ctx : EvalContext inner outer) -> SnocView ctx
  snocView [] = [<]
  snocView (hd :: ctx@_) with (snocView ctx)
    _ | [<] = [] :< hd
    _ | ctx' :< t = (hd :: ctx') :< t

public export
plug : {a : Ty} -> EvalContext a b -> Closed a -> Closed b
plug [] f = f
plug (t :: ts) f = plug ts (ClApp f t)

public export
0 plugSnoc : (ctx : EvalContext a (Arr dom b)) ->
           (t : Closed dom) ->
           (f : Closed a) ->
           plug (snoc ctx t) f === ClApp (plug ctx f) t
plugSnoc [] _ _ = Refl
plugSnoc (t :: ctx) _ _ = plugSnoc ctx _ _

public export
data Decomposition : Closed a -> Type where
  Val : (sc : Term (a :: g) b) -> (env : Env g) ->
        Decomposition {a = Arr a b} (Closure (Lam sc) env)
  Red : {s : Ty} -> (r : Redex s) -> (ctx : EvalContext s t) ->
        Decomposition {a = t} (plug ctx (redex r))

public export
load : {a : Ty} -> (ctx : EvalContext a b) -> (c : Closed a) -> Decomposition (plug ctx c)
public export
unload : {a, b : Ty} -> (ctx : EvalContext (Arr a b) outer) ->
         (sc : Term (a :: g) b) ->
         (env : Env g) ->
         Decomposition (plug ctx (Closure (Lam sc) env))

load ctx (ClApp f t) = load (t :: ctx) f
load ctx (Closure (Var v) env) = Red (RVar v env) ctx
load ctx (Closure (App f t) env) = Red (RApp f t env) ctx
load ctx (Closure (Lam sc) env) = unload ctx sc env

unload [] sc env = Val sc env
unload (arg :: ctx) sc env = Red (Beta sc env arg) ctx

public export
decompose : {a : Ty} -> (c : Closed a) -> Decomposition c
decompose = load []

public export
decomposePlug : {a : Ty} -> (ctx : EvalContext a b) -> (c : Closed a) ->
                decompose (plug ctx c) === load ctx c
decomposePlug [] c = Refl
decomposePlug (t :: ctx) c = decomposePlug ctx (ClApp c t)

public export
recompose : Decomposition {a} c -> Closed a
recompose (Red r ctx) = plug ctx (contract r)
recompose (Val sc env) = Closure (Lam sc) env

public export
headReduce : {a : Ty} -> Closed a -> Closed a
headReduce c = recompose (decompose c)

public export
loadRedex :
  (ctx : EvalContext a b) -> (r : Redex a) ->
  load ctx (redex r) === Red r ctx
loadRedex ctx (RVar _ _) = Refl
loadRedex ctx (RApp _ _ _) = Refl
loadRedex ctx (Beta _ _ _) = Refl


public export
headReducePlug :
  (ctx : EvalContext a b) -> (r : Redex a) ->
  headReduce (plug ctx (redex r)) === plug ctx (contract r)
headReducePlug ctx r
  = rewrite decomposePlug ctx (redex r) in
    rewrite loadRedex ctx r in
    Refl

headReduceNeutral :
  (ctx : EvalContext s b) -> (r : Redex s) ->
  (f : Closed (Arr a b)) -> Not (IsValue f) ->
  ClApp f t === plug ctx (redex r) ->
  plug ctx (contract r) === ClApp (headReduce f) t
headReduceNeutral ctx@_ r f nv with (snocView ctx)
  headReduceNeutral ctx@_ (RVar _ _) f nv | [<] = \case Refl impossible
  headReduceNeutral ctx@_ (RApp _ _ _) f nv | [<] = \case Refl impossible
  headReduceNeutral ctx@_ (Beta _ _ _) f nv | [<] = \Refl => absurd (nv Lam)
  _ | ctx' :< arg
    = rewrite plugSnoc ctx' arg (contract r) in
      rewrite plugSnoc ctx' arg (redex r) in
      \Refl =>
      rewrite headReducePlug ctx' r in
      Refl

public export
headReduceClApp : {a, b : Ty} ->
                  (f : Closed (Arr a b)) -> Not (IsValue f) -> (t : Closed a) ->
                  headReduce (ClApp f t) === ClApp (headReduce f) t
headReduceClApp f nv t with (decompose (ClApp f t)) | (ClApp f t) proof eq
  _ | Val sc env | .(Closure (Lam sc) env)
    = case eq of { Refl impossible }
  _ | Red r ctx | plug ctx (redex r)
    = headReduceNeutral ctx r f nv eq

------------------------------------------------------------------------
-- Section 4: Iterated head reduction

namespace Naïve

  covering
  evaluate : {a : Ty} -> Closed a -> Value a
  evaluate c = iterate (decompose c) where

    iterate : {a : Ty} -> {0 c : Closed a} -> Decomposition c -> Value a
    iterate (Val b env)
       -- there's a typo in the paper for this case
      = Val (Closure (Lam b) env) Lam
    iterate (Red r ctx) = iterate (decompose (plug ctx (contract r)))

-- Using the Bove-Capretta technique

public export
data Trace : Decomposition c -> Type where
  Done : (sc, env : _) -> Trace (Val sc env)
  Step : (ctx : EvalContext a b) -> (r : Redex a) ->
         Trace (decompose (plug ctx (contract r))) -> Trace (Red r ctx)

public export
iterate : {a : Ty} -> {0 c : Closed a} -> {d : Decomposition {a} c} ->
          (0 _ : Trace d) -> Value a
iterate (Done sc env) = Val (Closure (Lam sc) env) Lam
iterate (Step r ctx tr) = iterate tr

public export
Reducible : (a : Ty) -> Closed a -> Type
Reducible Base t = Trace (decompose t)
Reducible (Arr a b) t
  = (Trace (decompose t)
  , (x : Closed a) -> Reducible a x -> Reducible b (ClApp t x))

namespace ReducibleEnv

  public export
  data ReducibleEnv : Env g -> Type where
    Nil : ReducibleEnv []
    (::) : Reducible a t -> ReducibleEnv env -> ReducibleEnv (t :: env)

  public export
  lookup : ReducibleEnv env -> (v : Elem a g) -> Reducible a (lookup env v)
  lookup (red :: _) Here = red
  lookup (_ :: reds) (There v) = lookup reds v

public export
step : {a : Ty} -> {c : Closed a} -> Trace (decompose (headReduce c)) -> Trace (decompose c)
step {c = c@_} tr with (decompose c)
  _ | Val sc env = tr
  _ | Red r ctx = Step ctx r tr

public export
expand : {a : Ty} -> {c : Closed a} -> Reducible a (headReduce c) -> Reducible a c
expand {a = Base} tr = step tr
expand {a = Arr a b} {c = Closure (Lam x) env} (tr, hored) = (step tr, hored)
expand {a = Arr a b} {c = Closure (App x t) env} (tr, hored)
  = (step tr, \ arg, red => expand (hored arg red))
expand {a = Arr a b} {c = Closure (Var x) env} (tr, hored)
  = (step tr, \ arg, red => expand (hored arg red))
expand {a = Arr a b} {c = ClApp f t} (tr, hored)
  = MkPair (step tr)
  $ \ arg, red =>
    let 0 eq = headReduceClApp (ClApp f t) (\case Lam impossible) arg in
    let red = replace {p = Reducible b} (sym eq) (hored arg red) in
    expand {c = ClApp (ClApp f t) arg} red

public export
closure : {a : Ty} -> (t : Term g a) -> {env : Env g} ->
          ReducibleEnv env -> Reducible _ (Closure t env)
closure (Lam b) reds = (Done b _, \ arg, red => expand (closure b (red :: reds)))
closure (App f t) reds = expand (snd (closure f reds) (Closure t env) (closure t reds))
closure (Var v) reds = expand (lookup reds v)

public export
theorem : {a : Ty} -> (c : Closed a) -> Reducible a c
public export
theoremEnv : (env : Env g) -> ReducibleEnv env

theorem (Closure t env) = closure t (theoremEnv env)
theorem (ClApp f t) = snd (theorem f) t (theorem t)

theoremEnv [] = []
theoremEnv (t :: env) = theorem t :: theoremEnv env

public export
termination : {a : Ty} -> (c : Closed a) -> Trace (decompose c)
termination {a = Base} c = theorem c
termination {a = Arr a b} c = fst (theorem c)

public export
evaluate : {a : Ty} -> Closed a -> Value a
evaluate c = iterate (termination c)

------------------------------------------------------------------------
-- Section 5: Refocusing

public export
refocus : {a : Ty} -> (ctx : EvalContext a b) -> (c : Closed a) -> Decomposition (plug ctx c)
refocus ctx (ClApp f t) = refocus (t :: ctx) f
refocus ctx (Closure (App f t) env) = Red (RApp f t env) ctx
refocus ctx (Closure (Var v) env) = Red (RVar v env) ctx
refocus [] (Closure (Lam b) env) = Val b env
refocus (t :: ctx) (Closure (Lam b) env) = Red (Beta b env t) ctx

public export
refocusCorrect : {a : Ty} -> (ctx : EvalContext a b) -> (c : Closed a) ->
                 refocus ctx c === decompose (plug ctx c)
refocusCorrect ctx (ClApp f t) = refocusCorrect (t :: ctx) f
refocusCorrect ctx (Closure (App f t) env) = sym $ decomposePlug ctx (Closure (App f t) env)
refocusCorrect ctx (Closure (Var v) env) = sym $ decomposePlug ctx (Closure (Var v) env)
refocusCorrect [] (Closure (Lam b) env) = Refl
refocusCorrect (t :: ctx) (Closure (Lam b) env) = sym $ decomposePlug (t :: ctx) (Closure (Lam b) env)

namespace Refocus

  public export
  data Trace : {c : Closed a} -> Decomposition c -> Type where
    Done : (0 sc, env : _) -> Trace (Val sc env)
    Step : (0 ctx : EvalContext a b) -> (0 r : Redex a) ->
           Refocus.Trace (refocus ctx (contract r)) -> Trace (Red r ctx)

  public export
  trace : {0 c : Closed a} -> {0 d, e : Decomposition c} ->
          Krivine.Trace d -> (0 _ : e === d) -> Refocus.Trace e
  trace (Done sc env) Refl = Done sc env
  trace (Step ctx r tr) Refl
    = Step ctx r $ trace tr (refocusCorrect ctx (contract r))

  public export
  termination : {a : Ty} -> (c : Closed a) -> Refocus.Trace (decompose c)
  termination c = trace (termination c) Refl

  public export
  iterate : {d : Decomposition {a} c} -> (0 _ : Refocus.Trace d) -> Value a
  iterate (Done sc env) = Val (Closure (Lam sc) env) Lam
  iterate (Step ctx r tr) = iterate tr

  public export
  evaluate : {a : Ty} -> Closed a -> Value a
  evaluate c = iterate (Refocus.termination c)

------------------------------------------------------------------------
-- Section 6: The Krivine machine

public export
IsValidEnv : Env g -> Type

public export
IsValidClosed : Closed a -> Type

IsValidClosed (Closure t env) = IsValidEnv env
IsValidClosed _ = Void

IsValidEnv [] = ()
IsValidEnv (t :: env) = (IsValidClosed t, IsValidEnv env)

public export
ValidEnv : Context -> Type
ValidEnv g = Subset (Env g) IsValidEnv

public export
ValidClosed : Ty -> Type
ValidClosed a = Subset (Closed a) IsValidClosed

namespace ValidClosed

  public export
  Closure : Term g a -> ValidEnv g -> ValidClosed a
  Closure t (Element env pr) = Element (Closure t env) pr

  public export
  fstClosure : (t : Term g a) -> (env : ValidEnv g) ->
               fst (Closure t env) === Closure t (fst env)
  fstClosure t (Element env p) = Refl

  public export
  0 getContext : ValidClosed a -> Context
  getContext (Element (Closure {g} t env) _) = g

  public export
  getEnv : (c : ValidClosed a) -> ValidEnv (getContext c)
  getEnv (Element (Closure {g} _ env) pr) = Element env pr

  public export
  getTerm : (c : ValidClosed a) -> Term (getContext c) a
  getTerm (Element (Closure t _) _) = t

  public export
  etaValidClosed : (c : ValidClosed a) -> c === Closure (getTerm c) (getEnv c)
  etaValidClosed (Element (Closure t env) _) = Refl

namespace ValidEnv

  public export
  lookup : (env : ValidEnv g) -> Elem a g -> ValidClosed a
  lookup (Element (t :: env) p) Here = Element t (fst p)
  lookup (Element (t :: env) p) (There v) = lookup (Element env (snd p)) v

  public export
  fstLookup : (env : ValidEnv g) -> (v : Elem a g) ->
              fst (lookup env v) === lookup (fst env) v
  fstLookup (Element (t :: env) p) Here = Refl
  fstLookup (Element (t :: env) p) (There v) = fstLookup (Element env (snd p)) v

  public export
  Nil : ValidEnv []
  Nil = Element [] ()

  public export
  (::) : {a : Ty} -> ValidClosed a -> ValidEnv g -> ValidEnv (a :: g)
  Element t p :: Element env q = Element (t :: env) (p, q)

public export
IsValidEvalContext : EvalContext a b -> Type
IsValidEvalContext [] = ()
IsValidEvalContext (t :: ctx) =  (IsValidClosed t, IsValidEvalContext ctx)

public export
ValidEvalContext : (a, b : Ty) -> Type
ValidEvalContext a b = Subset (EvalContext a b) IsValidEvalContext

namespace ValidEvalContext

  public export
  Nil : ValidEvalContext a a
  Nil = Element [] ()

  public export
  (::) : ValidClosed a -> ValidEvalContext b c -> ValidEvalContext (Arr a b) c
  Element t p :: Element ctx q = Element (t :: ctx) (p, q)

  public export
  fstCons : (t : ValidClosed a) -> (ctx : ValidEvalContext b c) ->
            fst (t :: ctx) === fst t :: fst ctx
  fstCons (Element t p) (Element ctx q) = Refl

  public export
  [CONS] Biinjective ValidEvalContext.(::) where
    biinjective
      {x = Element t p} {y = Element t p}
      {v = Element ts ps} {w = Element ts ps}
      Refl = (Refl, Refl)

namespace ValidEvalContextView

  public export
  data View : ValidEvalContext a b -> Type where
    Nil : View []
    (::) : (t : ValidClosed a) -> (ctx : ValidEvalContext b c) ->
           View (t :: ctx)

  public export
  irrelevantUnit : (t : ()) -> t === ()
  irrelevantUnit () = Refl

  public export
  etaPair : (p : (a, b)) -> p === (fst p, snd p)
  etaPair (x, y) = Refl

  public export
  view : (ctx : ValidEvalContext a b) -> View ctx
  view (Element [] p) = rewrite irrelevantUnit p in []
  view (Element (t :: ctx) p)
    = rewrite etaPair p in
      Element t (fst p) :: Element ctx (snd p)

namespace Machine

  public export
  data Trace : Term g a -> ValidEnv g -> ValidEvalContext a b -> Type where

    Var : {env : ValidEnv g} -> {v : Elem a g} ->
          Trace (getTerm (lookup env v)) (getEnv (lookup env v)) ctx ->
          Trace (Var v) env ctx

    App : {f : Term g (Arr a b)} -> {t : Term g a} ->
          Trace f env (Closure t env :: ctx) ->
          Trace (App f t) env ctx

    Beta : {sc : Term (a :: g) b} ->
           {arg : ValidClosed a} ->
           {ctx : ValidEvalContext b c} ->
           Trace sc (arg :: env) ctx ->
           Trace (Lam sc) env (arg :: ctx)

    Done : Trace (Lam sc) env []

  data View : Trace t env ctx -> Type where
    VVar : {0 env : ValidEnv g} -> {0 v : Elem a g} ->
           (0 tr : Trace (getTerm (lookup env v)) (getEnv (lookup env v)) ctx) ->
           View {t = Var v, env, ctx} (Var tr)
    VApp : {0 f : Term g (Arr a b)} -> {0 t : Term g a} ->
           {0 ctx : ValidEvalContext b c} ->
           (0 tr : Trace f env (Closure t env :: ctx)) ->
           View (App {f, t, env, ctx} tr)
    VBeta : {0 sc : Term (a :: g) b} ->
            {arg : ValidClosed a} ->
            {ctx : ValidEvalContext b c} ->
            (0 tr : Trace sc (arg :: env) ctx) ->
            View (Beta {sc, arg, env, ctx} tr)
    VDone : (sc : Term (a :: g) b) ->
            View (Done {sc})

  public export
  vvar : (tr : Trace (Var v) env ctx) ->
         (tr' : Trace ? ? ctx ** tr = Var tr')
  vvar (Var tr) = (tr ** Refl)

  public export
  vapp : (tr : Trace (App f t) env ctx) ->
         (tr' : Trace f env (Closure t env :: ctx) ** tr = App tr')
  vapp (App tr) = (tr ** Refl)

  public export
  vlam0 : (eq : ctx = []) -> (tr : Trace (Lam sc) env ctx) -> tr ~=~ Machine.Done {sc, env}
  vlam0 eq Done = Refl
  vlam0 eq (Beta {arg = Element _ _, ctx = Element _ _} _) impossible

  public export
  vlamS : {0 env : ValidEnv g} -> {0 arg : ValidClosed a} ->
          {0 sc : Term (a :: g) b} -> {0 ctx' : ValidEvalContext b c} ->
          (eq : ctx = ValidEvalContext.(::) arg ctx') ->
          (tr : Trace (Lam sc) env ctx) ->
          (tr' : Trace sc (arg :: env) ctx' ** tr ~=~ Machine.Beta {sc, arg, env} tr')
  vlamS {arg = (Element _ _)} {ctx' = (Element _ _)} eq Done impossible
  vlamS eq (Beta tr) with 0 (fst (biinjective @{CONS} eq))
    _ | Refl with 0 (snd (biinjective @{CONS} eq))
      _ | Refl = (tr ** Refl)

  public export
  view : (t : Term g a) -> (env : ValidEnv g) -> (ctx : ValidEvalContext a b) ->
         (0 tr : Trace t env ctx) -> View tr
  view (Var v) env ctx tr = rewrite snd (vvar tr) in VVar _
  view (App f t) env ctx tr = rewrite snd (vapp tr) in VApp _
  view (Lam sc) env ctx@_ tr with (view ctx)
    _ | [] = rewrite vlam0 Refl tr in VDone sc
    _ | (arg :: ctx') = rewrite snd (vlamS {env, arg, sc, ctx'} Refl tr) in VBeta _

  public export
  refocus : {a : Ty} ->
    {t : Term g a} -> {env : ValidEnv g} ->
    {ctx : ValidEvalContext a b} ->
    (0 _ : Trace t env ctx) -> Value b
  refocus tr@_ with (view _ _ _ tr)
    _ | VVar tr' = refocus tr'
    _ | VApp tr' = refocus tr'
    _ | VBeta tr' = refocus tr'
    _ | VDone sc = Val (Closure (Lam sc) (fst env)) Lam

  -- This is way TOO nasty because we don't have eta for records :((
  public export
  correctness :
    {a : Ty} ->
    (ctx : ValidEvalContext a b) ->
    (t : Term g a) ->
    (env : ValidEnv g) ->
    (trold : Refocus.Trace (refocus (fst ctx) (Closure t (fst env)))) ->
    (trnew : Machine.Trace t env ctx) ->
    refocus trnew === Refocus.iterate trold
  correctness ctx (Var v) env (Step (fst ctx) (RVar v (fst env)) trold) (Var trnew)
    with (lookup env v) proof eq
    _ | Element (Closure t' env') penv'
    = correctness ctx t' (Element env' penv')
        (rewrite sym (cong fst eq) in rewrite fstLookup env v in trold)
        trnew
  correctness ctx (App f t) env (Step (fst ctx) (RApp f t (fst env)) trold) (App trnew)
    = correctness (Closure t env :: ctx) f env
        (rewrite fstCons (Closure t env) ctx in rewrite fstClosure t env in trold)
        trnew
  correctness .(Element arg parg :: Element ctx pctx) (Lam sc) (Element env penv)
    (Step ctx (Beta sc env arg) trold)
    (Beta {arg = Element arg parg, ctx = Element ctx pctx} trnew)
    = correctness (Element ctx pctx) sc (Element arg parg :: Element env penv)
        trold
        trnew
  correctness (Element [] _) (Lam sc) env (Done _ _) tr
    -- DISGUSTING
    = case tr of
        Beta {arg = Element _ _, ctx = Element _ _} _ impossible
        Done => Refl

  -- Another disgusgint proof because of a mix of:
  --   * lack of eta and the coverage
  --   * invalid "Dot pattern not valid here (Not LHS)" on the LHS
  --   * coverage checker being confused
  public export
  trace : {a : Ty} -> (ctx : ValidEvalContext a b) ->
          (t : Term g a) -> (env : ValidEnv g) ->
          Refocus.Trace (refocus (fst ctx) (Closure t (fst env))) ->
          Trace t env ctx
  trace ctx (Var v) env (Step (fst ctx) (RVar v (fst env)) tr)
    with (fstLookup env v) | (lookup env v) proof eq
    _ | lemma | Element (Closure t' env') p
      with (lookup (fst env) v)
      trace ctx (Var v) env (Step (fst ctx) (RVar v (fst env)) tr)
        | Refl | Element (Closure t' env') penv' | .(Closure t' env')
        = Var (rewrite eq in trace ctx t' (Element env' penv') tr)
  trace (Element ctx pctx) (App f t) (Element env penv) (Step .(ctx) (RApp f t env) tr)
    = App (trace (Closure t (Element env penv) :: Element ctx pctx) f (Element env penv) tr)
  trace (Element (arg :: ctx) pctx) (Lam sc) (Element env penv) tr
    = case tr of
        Done _ _ impossible
        (Step ctx (Beta sc env arg) tr) =>
          rewrite etaPair pctx in
          Beta {arg = Element arg (fst pctx), ctx = Element ctx (snd pctx)}
          (trace (Element ctx (snd pctx)) sc (Element (arg :: env) (fst pctx, penv)) tr)
  trace (Element [] pctx) (Lam sc) env tr
    = case tr of
        Beta {arg = Element _ _, ctx = Element _ _} _ impossible
        Done sc .(fst env) => rewrite irrelevantUnit pctx in Done

  public export
  termination : {a : Ty} -> (t : Term [] a) -> Trace t [] []
  termination t
    = trace [] t []
    $ rewrite refocusCorrect [] (Closure t []) in
      Refocus.termination (Closure t [])

  public export
  evaluate : {a : Ty} -> Term [] a -> Value a
  evaluate t = Machine.refocus (termination t)
