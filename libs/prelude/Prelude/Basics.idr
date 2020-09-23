module Prelude.Basics

import Builtin

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
the : (0 a : Type) -> (1 x : a) -> a
the _ x = x

||| Identity function.
public export %inline
id : (1 x : a) -> a           -- Hopefully linearity annotation won't
                              -- break equality proofs involving id
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

-- $ is compiled specially to shortcut any tricky unification issues, but if
-- it did have a type this is what it would be, and it might be useful to
-- use directly sometimes (e.g. in higher order functions)
public export
($) : forall a, b . ((x : a) -> b x) -> (x : a) -> b x
($) f a = f a

-------------------
-- PROOF HELPERS --
-------------------

||| Equality is a congruence.
public export
cong : (0 f : t -> u) -> (1 p : a = b) -> f a = f b
cong f Refl = Refl

||| Two-holed congruence.
export
-- These are natural in equational reasoning.
cong2 : (0 f : t1 -> t2 -> u) -> (1 p1 : a = b) -> (1 p2 : c = d) -> f a c = f b d
cong2 f Refl Refl = Refl

--------------
-- BOOLEANS --
--------------

||| Boolean Data Type.
public export
data Bool = True | False

||| Boolean NOT.
public export
not : (1 b : Bool) -> Bool
not True = False
not False = True

||| Boolean AND only evaluates the second argument if the first is `True`.
public export
(&&) : (1 b : Bool) -> Lazy Bool -> Bool
(&&) True x = x
(&&) False x = False

||| Boolean OR only evaluates the second argument if the first is `False`.
public export
(||) : (1 b : Bool) -> Lazy Bool -> Bool
(||) True x = True
(||) False x = x

||| Non-dependent if-then-else
public export
ifThenElse : (1 b : Bool) -> Lazy a -> Lazy a -> a
ifThenElse True l r = l
ifThenElse False l r = r

%inline
public export
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True
