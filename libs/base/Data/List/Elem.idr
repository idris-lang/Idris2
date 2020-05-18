module Data.List.Elem

import Decidable.Equality

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
thereInjective : {0 e1, e2 : Elem x xs} -> There e1 = There e2 -> e1 = e2
thereInjective Refl = Refl

export
DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There later) = No absurd
  decEq (There later) Here = No absurd
  decEq (There this) (There that) with (decEq this that)
    decEq (There this) (There this) | Yes Refl  = Yes Refl
    decEq (There this) (There that) | No contra = No (contra . thereInjective)

export
Uninhabited (Elem {a} x []) where
  uninhabited Here impossible
  uninhabited (There p) impossible

||| An item not in the head and not in the tail is not in the list at all.
export
neitherHereNorThere : Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xny xnxs  Here       = xny Refl
neitherHereNorThere xny xnxs (There xxs) = xnxs xxs

||| Check whether the given element is a member of the given list.
export
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
dropElem (x :: ys)  Here     = ys
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
indexElem  Z    (y :: ys) = Just (y ** Here)
indexElem (S n) (y :: ys) = map (\(x ** p) => (x ** There p)) (indexElem n ys)
