module Data.SnocList.Elem

import Data.Singleton
import Data.SnocList
import Decidable.Equality
import Control.Function

||| A proof that some element is found in a list.
public export
data Elem : a -> SnocList a -> Type where
  ||| A proof that the element is at the head of the list
  Here : Elem x (sx :< x)
  ||| A proof that the element is in the tail of the list
  There : {0 x, y : a} -> Elem x sx -> Elem x (sx :< y)

export
Uninhabited (Here {x} {sx} = There {x = x'} {y} {sx = sx'} e) where
  uninhabited Refl impossible

export
Uninhabited (There {x} {y} {sx} e = Here {x = x'} {sx = sx'}) where
  uninhabited Refl impossible

export
Injective (There {x} {y} {sx}) where
  injective Refl = Refl

export
DecEq (Elem x sx) where
  decEq Here Here = Yes Refl
  decEq (There this) (There that) = decEqCong $ decEq this that
  decEq Here (There later) = No absurd
  decEq (There later) Here = No absurd

public export
Uninhabited (Elem {a} x [<]) where
  uninhabited Here impossible
  uninhabited (There p) impossible

||| An item not in the head and not in the tail is not in the list at all.
public export
neitherHereNorThere : Not (x = y) -> Not (Elem x sx) -> Not (Elem x (sx :< y))
neitherHereNorThere xny _ Here = xny Refl
neitherHereNorThere _ xnxs (There xxs) = xnxs xxs

||| Check whether the given element is a member of the given list.
public export
isElem : DecEq a => (x : a) -> (sx : SnocList a) -> Dec (Elem x sx)
isElem x [<] = No absurd
isElem x (sx :< y) with (decEq x y)
  isElem x (sx :< x) | Yes Refl = Yes Here
  isElem x (sx :< y) | No xny with (isElem x sx)
    isElem x (sx :< y) | No xny | Yes xsx = Yes (There xsx)
    isElem x (sx :< y) | No xny | No xnsx = No (neitherHereNorThere xny xnsx)

||| Get the element at the given position.
public export
get : (sx : SnocList a) -> (p : Elem x sx) -> a
get (_ :< x) Here = x
get (sx :< _) (There p) = get sx p

||| Get the element at the given position, with proof that it is the desired element.
public export
lookup : (sx : SnocList a) -> (p : Elem x sx) -> Singleton x
lookup (_ :< x) Here = Val x
lookup (sx :< _) (There p) = lookup sx p

||| Remove the element at the given position.
public export
dropElem : (sx : SnocList a) -> (p : Elem x sx) -> SnocList a
dropElem (sy :< _) Here = sy
dropElem (sy :< y) (There p) = (dropElem sy p) :< y

||| Erase the indices, returning the numeric position of the element
public export
elemToNat : Elem x sx -> Nat
elemToNat Here = Z
elemToNat (There p) = S (elemToNat p)

||| Find the element with a proof at a given position (in reverse), if it is valid
public export
indexElem : Nat -> (sx : SnocList a) -> Maybe (x ** Elem x sx)
indexElem _ [<] = Nothing
indexElem Z (_ :< y) = Just (y ** Here)
indexElem (S k) (sy :< _) = (\(y ** p) => (y ** There p)) `map` (indexElem k sy)

||| Lift the membership proof to a mapped list
export
elemMap : (0 f : a -> b) -> Elem x sx -> Elem (f x) (map f sx)
elemMap f Here = Here
elemMap f (There el) = There $ elemMap f el
