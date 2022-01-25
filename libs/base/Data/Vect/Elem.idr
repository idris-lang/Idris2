module Data.Vect.Elem

import Data.Vect
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Vector membership proof
--------------------------------------------------------------------------------

||| A proof that some element is found in a vector
public export
data Elem : a -> Vect k a -> Type where
  Here : Elem x (x::xs)
  There : (later : Elem x xs) -> Elem x (y::xs)

export
Uninhabited (Here = There e) where
  uninhabited Refl impossible

export
Uninhabited (There e = Here) where
  uninhabited Refl impossible

export
Uninhabited (Elem x []) where
  uninhabited Here impossible

export
Uninhabited (x = z) => Uninhabited (Elem z xs) => Uninhabited (Elem z $ x::xs) where
  uninhabited Here @{xz} = uninhabited Refl @{xz}
  uninhabited (There y) = uninhabited y

||| An item not in the head and not in the tail is not in the Vect at all
export
neitherHereNorThere : Not (x = y) -> Not (Elem x xs) -> Not (Elem x (y :: xs))
neitherHereNorThere xneqy xninxs  Here         = xneqy Refl
neitherHereNorThere xneqy xninxs (There xinxs) = xninxs xinxs

||| A decision procedure for Elem
public export
isElem : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
isElem x [] = No uninhabited
isElem x (y::xs) with (decEq x y)
  isElem x (x::xs) | (Yes Refl) = Yes Here
  isElem x (y::xs) | (No xneqy) with (isElem x xs)
    isElem x (y::xs) | (No xneqy) | (Yes xinxs) = Yes (There xinxs)
    isElem x (y::xs) | (No xneqy) | (No xninxs) = No (neitherHereNorThere xneqy xninxs)

public export
replaceElem : (xs : Vect k t) -> Elem x xs -> (y : t) -> (ys : Vect k t ** Elem y ys)
replaceElem (x::xs) Here y = (y :: xs ** Here)
replaceElem (x::xs) (There xinxs) y with (replaceElem xs xinxs y)
  replaceElem (x::xs) (There xinxs) y | (ys ** yinys) = (x :: ys ** There yinys)

public export
replaceByElem : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceByElem (x::xs)  Here         y = y :: xs
replaceByElem (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y

public export
mapElem : {0 xs : Vect k t} -> {0 f : t -> u} ->
          (1 _ : Elem x xs) -> Elem (f x) (map f xs)
mapElem  Here     = Here
mapElem (There e) = There (mapElem e)

||| Remove the element at the given position.
|||
||| @xs The vector to be removed from
||| @p A proof that the element to be removed is in the vector
public export
dropElem : {k : _} -> (xs : Vect (S k) t) -> Elem x xs -> Vect k t
dropElem           (x::ys)  Here         = ys
dropElem {k = S k} (x::ys) (There later) = x :: dropElem ys later

||| Erase the indices, returning the bounded numeric position of the element
public export
elemToFin : {0 xs : Vect n a} -> Elem x xs -> Fin n
elemToFin  Here     = FZ
elemToFin (There p) = FS (elemToFin p)

||| Find the element with a proof at a given bounded position
public export
indexElem : (1 _ : Fin n) -> (xs : Vect n a) -> (x ** Elem x xs)
indexElem  FZ    (y::_)  = (y ** Here)
indexElem (FS n) (_::ys) = let (x ** p) = indexElem n ys in
                           (x ** There p)
