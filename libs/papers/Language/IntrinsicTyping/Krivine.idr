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
  ClApp : Closed (Arr a b) -> Closed a -> Closed b

public export
data Env : Context -> Type where
  Nil : Env []
  (::) : Closed a -> Env g -> Env (a :: g)

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
  Beta : Term (a :: g) b -> Env g -> Closed a -> Redex b

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
plug : EvalContext a b -> Closed a -> Closed b
plug [] f = f
plug (t :: ts) f = plug ts (ClApp f t)

public export
data Decomposition : Closed a -> Type where
  Val : (sc : Term (a :: g) b) -> (env : Env g) ->
        Decomposition {a = Arr a b} (Closure (Lam sc) env)
  Red : (r : Redex s) -> (ctx : EvalContext s t) ->
        Decomposition {a = t} (plug ctx (redex r))

public export
load : (ctx : EvalContext a b) -> (c : Closed a) -> Decomposition (plug ctx c)
public export
unload : (ctx : EvalContext (Arr a b) outer) ->
         (sc : Term (a :: g) b) ->
         (env : Env g) ->
         Decomposition (plug ctx (Closure (Lam sc) env))

load ctx (Closure (Lam sc) env) = unload ctx sc env
load ctx (Closure (App f t) env) = Red (RApp f t env) ctx
load ctx (Closure (Var v) env) = Red (RVar v env) ctx
load ctx (ClApp f t) = load (t :: ctx) f

unload [] sc env = Val sc env
unload (arg :: ctx) sc env = Red (Beta sc env arg) ctx

public export
decompose : (c : Closed a) -> Decomposition c
decompose = load []

public export
headReduce : Closed a -> Closed a
headReduce c@_ with (decompose c)
  _ | Val b env = Closure (Lam b) env
  _ | Red r ctx = plug ctx (contract r)

------------------------------------------------------------------------
-- Section 4: Iterated head reduction

namespace Naïve

  covering
  evaluate : Closed a -> Value a
  evaluate c = iterate (decompose c) where

    iterate : {0 a : Ty} -> {0 c : Closed a} -> Decomposition c -> Value a
    iterate (Val b env)
       -- there's a typo in the paper for this case
      = Val (Closure (Lam b) env) Lam
    iterate (Red r ctx) = iterate (decompose (plug ctx (contract r)))

-- Using the Bove-Capretta technique

public export
data Trace : Decomposition c -> Type where
  Done : (0 sc, env : _) -> Trace (Val sc env)
  Step : (0 ctxt, r : _) -> Trace (decompose (plug ctx (contract r))) -> Trace (Red r ctx)

public export
iterate : {d : Decomposition {a} c} -> (0 _ : Trace d) -> Value a
iterate (Done sc env) = Val (Closure (Lam sc) env) Lam
iterate (Step r ctx tr) = iterate tr

public export
Reducible : (a : Ty) -> Closed a -> Type
Reducible Base t = Trace (decompose t)
Reducible (Arr a b) t
  = (Trace (decompose t)
  , (x : Closed a) -> Reducible a x -> Reducible b (ClApp t x))

public export
ReducibleEnv : {g : _} -> Env g -> Type
ReducibleEnv [] = ()
ReducibleEnv (t :: env) = (Reducible _ t, ReducibleEnv env)

public export
expand : {a : Ty} -> {c : Closed a} -> Reducible a (headReduce c) -> Reducible a c
expand {a = Base} {c = Closure sc env} red = ?Ag_2
expand {a = Base} {c = ClApp f t} red = ?Ag_3
expand {a = Arr a b} {c = c} red = ?Ag_1

namespace Reducible

  public export
  lookup : {env : _} -> ReducibleEnv env -> (v : Elem a g) -> Reducible a (lookup env v)
  lookup {env = _ :: _} (red, _) Here = red
  lookup {env = _ :: _} (_, reds) (There v) = Reducible.lookup reds v

public export
closure : {a : Ty} -> (t : Term g a) -> {env : Env g} ->
          ReducibleEnv env -> Reducible _ (Closure t env)
closure (Lam b) reds = (Done b _, \ arg, red => expand (closure b (red, reds)))
closure (App f t) reds = expand (snd (closure f reds) (Closure t env) (closure t reds))
closure (Var v) reds = expand (Reducible.lookup reds v)
