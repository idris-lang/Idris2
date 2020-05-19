-- a mini prelude

module Stuff

public export
data Bool = True | False

public export
not : Bool -> Bool
not True = False
not False = True

public export
data Maybe a = Nothing | Just a

public export
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

public export
ifThenElse : Bool -> Lazy a -> Lazy a -> a
ifThenElse True t e = t
ifThenElse False t e = e

public export
data Nat = Z | S Nat

public export
fromInteger : Integer -> Nat
fromInteger x = ifThenElse (intToBool (prim__eq_Integer x 0))
                      Z (S (fromInteger (prim__sub_Integer x 1)))

public export
plus : Nat -> Nat -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

infixr 5 ::

public export
data List a = Nil | (::) a (List a)

public export
data Equal : a -> b -> Type where
     Refl : (0 x : a) -> Equal x x

public export
data Unit = MkUnit

public export
data Pair : Type -> Type -> Type where
     MkPair : {0 a, b : Type} -> (1 x : a) -> (1 y : b) -> Pair a b

public export
data Unrestricted : Type -> Type where
     Un : (x : a) -> Unrestricted a

public export
the : (a : Type) -> a -> a
the _ x = x
