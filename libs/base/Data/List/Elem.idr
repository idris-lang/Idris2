module Data.List.Elem

import Decidable.Equality
import Control.Function

%default total

--------------------------------------------------------------------------------
-- List membership proof
--------------------------------------------------------------------------------

||| A proof that some element is found in a list.
public export
data Elem : a -> List a -> Type where
     ||| A proof that the element is at the head of the list
     Here : Elem x (x :: xs)
     ||| A proof that the element is in the tail of the list
     There : Elem x xs -> Elem x (y :: xs)

export
Uninhabited (Here = There e) where
  uninhabited Refl impossible

export
Uninhabited (There e = Here) where
  uninhabited Refl impossible

export
Injective (There {x} {y} {xs}) where
  injective Refl = Refl

export
DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq (There this) (There that) = decEqCong $ decEq this that
  decEq Here (There later) = No absurd
  decEq (There later) Here = No absurd

export
Uninhabited (Elem {a} x []) where
  uninhabited Here impossible
  uninhabited (There p) impossible

export
Uninhabited (x = z) => Uninhabited (Elem z xs) => Uninhabited (Elem z $ x::xs) where
  uninhabited Here @{xz} = uninhabited Refl @{xz}
  uninhabited (There y) = uninhabited y

||| An item not in the head and not in the tail is not in the list at all.
export
neitherHereNorThere : Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xny _     Here        = xny Refl
neitherHereNorThere _   xnxs  (There xxs) = xnxs xxs

||| Check whether the given element is a member of the given list.
public export
isElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
isElem x [] = No absurd
isElem x (y :: xs) with (decEq x y)
  isElem x (x :: xs) | Yes Refl = Yes Here
  isElem x (y :: xs) | No xny with (isElem x xs)
    isElem x (y :: xs) | No xny | Yes xxs = Yes (There xxs)
    isElem x (y :: xs) | No xny | No xnxs = No (neitherHereNorThere xny xnxs)

||| Remove the element at the given position.
public export
dropElem : (xs : List a) -> (p : Elem x xs) -> List a
dropElem (_ :: ys)  Here     = ys
dropElem (x :: ys) (There p) = x :: dropElem ys p

||| Erase the indices, returning the numeric position of the element
public export
elemToNat : Elem x xs -> Nat
elemToNat  Here     = Z
elemToNat (There p) = S (elemToNat p)

||| Find the element with a proof at a given position, if it is valid
public export
indexElem : Nat -> (xs : List a) -> Maybe (x ** Elem x xs)
indexElem  _    []        = Nothing
indexElem  Z    (y :: _)  = Just (y ** Here)
indexElem (S n) (_ :: ys) = map (\(x ** p) => (x ** There p)) (indexElem n ys)

||| Lift the membership proof to a mapped list
export
elemMap : (0 f : a -> b) -> Elem x xs -> Elem (f x) (map f xs)
elemMap f  Here      = Here
elemMap f (There el) = There $ elemMap f el
