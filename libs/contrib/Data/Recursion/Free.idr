||| Code corresponding to McBride's paper:
||| Turing-Completeness Totally Free
|||
||| It gives us a type to describe computation using general recursion
||| and functions to run these computations for a while or to completion
||| if we are able to prove them total.

module Data.Recursion.Free

import Data.Late
import Data.InductionRecursion.DybjerSetzer

%default total

------------------------------------------------------------------------
-- Type

||| Syntax for a program using general recursion
public export
data General : (a : Type) -> (b : a -> Type) -> (x : Type) -> Type where
  ||| We can return a value without performing any recursive call.
  Tell : x -> General a b x
  ||| Or we can pick an input and ask an oracle to give us a return value
  ||| for it. The second argument is a continuation explaining what we want
  ||| to do with the returned value.
  Ask  : (i : a) -> (b i -> General a b x) -> General a b x

||| Type of functions using general recursion
public export
PiG : (a : Type) -> (b : a -> Type) -> Type
PiG a b = (i : a) -> General a b (b i)

||| Recursor for General
public export
fold : (x -> y) -> ((i : a) -> (b i -> y) -> y) -> General a b x -> y
fold pure ask (Tell x) = pure x
fold pure ask (Ask i k) = ask i (\ o => fold pure ask (k o))

------------------------------------------------------------------------
-- Basic functions

||| Perform a recursive call and return the value provided by the oracle.
public export
call : PiG a b
call i = Ask i Tell

||| Monadic bind (defined outside of the interface to be able to use it for
||| map and (<*>)).
public export
bind : General a b x -> (x -> General a b y) -> General a b y
bind m f = fold f Ask m

||| Given a monadic oracle we can give a monad morphism interpreting a
||| function using general recursion as a monadic process.
public export
monadMorphism : Monad m => (t : (i : a) -> m (b i)) -> General a b x -> m x
monadMorphism t = fold pure (\ i => (t i >>=))

------------------------------------------------------------------------
-- Instances

public export
Functor (General a b) where
  map f = fold (Tell . f) Ask

public export
Applicative (General a b) where
  pure = Tell
  gf <*> gv = bind gf (\ f => map (f $) gv)

public export
Monad (General a b) where
  (>>=) = bind

------------------------------------------------------------------------
-- Fuel-based (partial) evaluation of a general program

||| Check whehther we are ready to return a value
public export
already : General a b x -> Maybe x
already = monadMorphism (\ i => Nothing)

||| Use a function using general recursion to expand all of the oracle calls.
public export
expand : PiG a b -> General a b x -> General a b x
expand f = monadMorphism f

||| Recursively call expand a set number of times.
public export
engine : PiG a b -> Nat -> General a b x -> General a b x
engine f Z     = id
engine f (S n) = engine f n . expand f

||| Check whether recursively calling expand a set number of times is enough
||| to produce a value.
public export
petrol : PiG a b -> Nat -> (i : a) -> Maybe (b i)
petrol f n i = already $ engine f n $ f i

------------------------------------------------------------------------
-- Late-based evaluation

||| Rely on an oracle using general recursion to convert a function using
||| general recursion into a process returning a value in the (distant) future.
public export
late : PiG a b -> General a b x -> Late x
late f = monadMorphism (\ i => Later (assert_total $ late f (f i)))

||| Interpret a function using general recursion as a process returning
||| a value in the (distant) future.
public export
lazy : PiG a b -> (i : a) -> Late (b i)
lazy f i = late f (f i)

------------------------------------------------------------------------
-- Domain and total evaluation function for a general program

||| Compute, as a code for an inductive-recursive type, the domain of a
||| function defined by general recursion.
public export
Domain : PiG a b -> (i : a) -> Code b (b i)
Domain f i = monadMorphism callInDom (f i) where

  callInDom : (i : a) -> Code b (b i)
  callInDom i = Branch () (const i) $ \ t => Yield (t ())

||| If a given input is in the domain of the function then we may evaluate
||| it fully on that input and obtain a pure return value.
public export
evaluate : (f : PiG a b) -> (i : a) -> Mu (Domain f) i -> b i
evaluate f i inDom = Decode inDom

||| If every input value is in the domain then the function is total.
public export
totally : (f : PiG a b) -> ((i : a) -> Mu (Domain f) i) ->
          (i : a) -> b i
totally f allInDomain i = evaluate f i (allInDomain i)
