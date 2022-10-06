module Data.SnocList.Elem

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
Uninhabited (Here = There e) where
  uninhabited Refl impossible

export
Uninhabited (There e = Here) where
  uninhabited Refl impossible

export
Uninhabited (Elem {a} x [<]) where
  uninhabited Here impossible
  uninhabited (There p) impossible

export
Injective (There {x} {y} {sx}) where
  injective Refl = Refl

export
DecEq (x `Elem` sx) where
  decEq Here Here = Yes Refl
  decEq (There y) (There z) = decEqCong $ decEq y z
  decEq Here (There _) = No absurd
  decEq (There _) Here = No absurd

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

||| An item not in the head and not in the tail is not in the list at all.
export
neitherHereNorThere : Not (x = y) -> Not (Elem x sx) -> Not (Elem x (sx :< y))
neitherHereNorThere xny _ Here = xny Refl
neitherHereNorThere _ xnxs (There xxs) = xnxs xxs
