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

infixl 4 &&

public export
(&&) : Bool -> Bool -> Bool
(&&) True x = x
(&&) False x = False

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
     Refl : {0 x : a} -> Equal x x

infix 9 ===, ~=~

public export
(===) : (x : a) -> (y : a) -> Type
(===) = Equal

public export
(~=~) : (x : a) -> (y : b) -> Type
(~=~) = Equal

public export
data Unit = MkUnit

namespace Builtin -- hardcoded in elaborator!
  public export
  data Pair : Type -> Type -> Type where
       MkPair : {0 a, b : Type} -> (1 x : a) -> (1 y : b) -> Pair a b

public export
fst : {0 a, b : Type} -> (a, b) -> a
fst (x, y) = x

public export
snd : {0 a, b : Type} -> (a, b) -> b
snd (x, y) = y

%pair Pair fst snd

namespace DPair
    public export
    data DPair : (a : Type) -> (a -> Type) -> Type where
         MkDPair : (x : a) -> prop x -> DPair a prop

    fst : DPair a p -> a
    fst (MkDPair x y) = x

    snd : (x : DPair a p) -> p (fst x)
    snd (MkDPair x y) = y

public export
data Unrestricted : Type -> Type where
     Un : (x : a) -> Unrestricted a

public export
the : (a : Type) -> a -> a
the _ x = x

public export
id : a -> a
id x = x

public export
data Void : Type where

public export
data Dec : Type -> Type where
     Yes : a -> Dec a
     No : (a -> Void) -> Dec a
