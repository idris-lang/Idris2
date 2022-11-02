||| The content of this module is based on the paper
||| From Mathematics to Abstract Machine
||| A formal derivation of an executable Krivine machine
||| by Wouter Swierstra

module Language.IntrinsicTyping.Krivine

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
    (:<) : (ctxt : EvalContext inner (Arr dom outer)) ->
           (t : Closed dom) ->
           SnocView (snoc ctxt t)

  public export
  snocView : (ctxt : EvalContext inner outer) -> SnocView ctxt
  snocView [] = [<]
  snocView (hd :: ctxt@_) with (snocView ctxt)
    _ | [<] = [] :< hd
    _ | ctxt' :< t = (hd :: ctxt') :< t

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
  Done : (0 sc, env : _) -> Trace (Val sc env)
  Step : (0 ctx : EvalContext a b) -> (0 r : Redex a) ->
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
