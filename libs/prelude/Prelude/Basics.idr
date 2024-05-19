module Prelude.Basics

import Builtin

import Prelude.Ops

%default total


||| `Not x` is an alias for `x -> Void`, indicating that any term of type `x`
||| leads to a contradiction. It can be used in conjunction with `void` or
||| `absurd`.
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
the : (0 a : Type) -> (1 x : a) -> a
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
public export %inline %tcinline
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g = \x => f (g x)

||| Composition of a two-argument function with a single-argument one.
||| `(.:)` is like `(.)` but the second argument and the result are two-argument functions.
||| This operator is also known as "blackbird operator".
public export %inline %tcinline
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
public export %tcinline
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g = \x, y => g x `f` g y

export infixl 0 `on`

||| Takes in the first two arguments in reverse order.
||| @ f the function to flip
public export %tcinline
flip : (f : a -> b -> c) -> b -> a -> c
flip f = \x, y => f y x

||| Function application.
public export %tcinline
apply : (a -> b) -> a -> b
apply f = \a => f a

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

||| Pipeline style function application, useful for chaining
||| functions into a series of transformations, reading top
||| to bottom.
|||
||| ```idris example
||| [[1], [2], [3]] |> join |> map (* 2)
||| ```
public export
(|>) : a -> (a -> b) -> b
a |> f = f a

||| Backwards pipeline style function application, similar to $.
|||
||| ```idris example
||| unpack <| "hello" ++ "world"
||| ```
public export
(<|) : (a -> b) -> a -> b
f <| a = f a

-------------------
-- PROOF HELPERS --
-------------------

||| Equality is a congruence.
public export
cong : (0 f : t -> u) -> (0 p : a = b) -> f a = f b
cong f Refl = Refl

||| Two-holed congruence.
export
-- These are natural in equational reasoning.
cong2 : (0 f : t1 -> t2 -> u) -> (0 p1 : a = b) -> (0 p2 : c = d) -> f a c = f b d
cong2 f Refl Refl = Refl

||| Dependent version of `cong`.
public export
depCong : {0 p : a -> Type} ->
          (0 f : (x : a) -> p x) ->
          {0 x1, x2 : a} ->
          (prf : x1 = x2) ->
          f x1 = f x2
depCong f Refl = Refl

||| Dependent version of `cong2`.
public export
depCong2 : {0 p : a -> Type} ->
           {0 q : (x : a) -> (y : p x) -> Type} ->
           (0 f : (x : a) -> (y : p x) -> q x y) ->
           {0 x1, x2 : a} -> (prfX : x1 = x2) ->
           {0 y1 : p x1} -> {y2 : p x2} ->
           (prfY : y1 = y2) -> f x1 y1 = f x2 y2
depCong2 f Refl Refl = Refl

||| Irrelevant equalities can always be made relevant
export
irrelevantEq : (0 _ : a ~=~ b) -> a ~=~ b
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
