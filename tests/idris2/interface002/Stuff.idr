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
data Eq : a -> b -> Type where
     Refl : (x : a) -> Eq x x

public export
data Unit = MkUnit

public export
data Pair : Type -> Type -> Type where
     MkPair : {0 a, b : Type} -> a -> b -> Pair a b

public export
the : (0 a : Type) -> a -> a
the _ x = x

public export
id : a -> a
id x = x
