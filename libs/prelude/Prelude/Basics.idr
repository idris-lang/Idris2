module Prelude.Basics

import Builtin

import Prelude.Ops

%default total

public export
Not : Type -> Type
Not x = x -> Void

-----------------------
-- UTILITY FUNCTIONS --
-----------------------

||| Manually assign a type to an expression.
||| @ a the type to assign
||| @ x the element to get the type
public export %inline
the : (0 a : Type) -> (x : a) -> a
the _ x = x

||| Identity function.
public export %inline
id : (x : a) -> a
id x = x

||| Function that duplicates its input
public export
dup : a -> (a, a)
dup x = (x, x)

||| Constant function.  Ignores its second argument.
public export %inline
const : a -> b -> a
const x = \value => x

||| Function composition.
public export %inline
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g = \x => f (g x)

||| Composition of a two-argument function with a single-argument one.
||| `(.:)` is like `(.)` but the second argument and the result are two-argument functions.
||| This operator is also known as "blackbird operator".
public export %inline
(.:) : (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)

||| `on b u x y` runs the binary function b on the results of applying
||| unary function u to two arguments x and y. From the opposite perspective,
||| it transforms two inputs and combines the outputs.
|||
||| ```idris example
||| ((+) `on` f) x y = f x + f y
||| ```
|||
||| Typical usage:
|||
||| ```idris example
||| sortBy (compare `on` fst).
||| ```
public export
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g = \x, y => g x `f` g y

infixl 0 `on`

||| Takes in the first two arguments in reverse order.
||| @ f the function to flip
public export
flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

||| Function application.
public export
apply : (a -> b) -> a -> b
apply f a = f a

public export
curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

public export
uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

||| ($) is compiled specially to shortcut any tricky unification issues, but if
||| it did have a type this is what it would be, and it might be useful to
||| use directly sometimes (e.g. in higher order functions)
public export
($) : forall a, b . ((x : a) -> b x) -> (x : a) -> b x
($) f a = f a

-------------------
-- PROOF HELPERS --
-------------------

||| Equality is a congruence.
public export
cong : (0 f : t -> u) -> (p : a = b) -> f a = f b
cong f Refl = Refl

||| Two-holed congruence.
export
-- These are natural in equational reasoning.
cong2 : (0 f : t1 -> t2 -> u) -> (p1 : a = b) -> (p2 : c = d) -> f a c = f b d
cong2 f Refl Refl = Refl

||| Irrelevant equalities can always be made relevant
export
irrelevantEq : (0 _ : a === b) -> a === b
irrelevantEq Refl = Refl

--------------
-- BOOLEANS --
--------------

||| Boolean Data Type.
public export
data Bool = False | True

||| Boolean NOT.
%inline
public export
not : (b : Bool) -> Bool
not True = False
not False = True

||| Boolean AND only evaluates the second argument if the first is `True`.
%inline
public export
(&&) : (b : Bool) -> Lazy Bool -> Bool
(&&) True x = x
(&&) False x = False

||| Boolean OR only evaluates the second argument if the first is `False`.
%inline
public export
(||) : (b : Bool) -> Lazy Bool -> Bool
(||) True x = True
(||) False x = x

||| Non-dependent if-then-else
%inline
public export
ifThenElse : (b : Bool) -> Lazy a -> Lazy a -> a
ifThenElse True l r = l
ifThenElse False l r = r

%inline
public export
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

--------------
-- LISTS    --
--------------

||| Generic lists.
public export
data List a =
  ||| Empty list
  Nil

  | ||| A non-empty list, consisting of a head element and the rest of the list.
  (::) a (List a)

%name List xs, ys, zs

||| Snoc lists.
public export
data SnocList a =
  ||| Empty snoc-list
  Lin

  | ||| A non-empty snoc-list, consisting of the rest of the snoc-list and the final element.
  (:<) (SnocList a) a

%name SnocList sx, sy, sz
