module Data.List.AtIndex

import Data.DPair
import Data.List.HasLength
import Data.Nat
import Decidable.Equality

%default total

||| @AtIndex witnesses the fact that a natural number encodes a membership proof.
||| It is meant to be used as a runtime-irrelevant gadget to guarantee that the
||| natural number is indeed a valid index.
public export
data AtIndex : Nat -> a -> List a -> Type where
  Z : AtIndex Z a (a :: as)
  S : AtIndex n a as -> AtIndex (S n) a (b :: as)

||| Inversion principle for Z constructor
export
inverseZ : AtIndex Z x (y :: xs) -> x === y
inverseZ Z = Refl

||| inversion principle for S constructor
export
inverseS : AtIndex (S n) x (y :: xs) -> AtIndex n x xs
inverseS (S p) = p

||| An empty list cannot possibly have members
export
Uninhabited (AtIndex n a []) where
  uninhabited Z impossible
  uninhabited (S _) impossible

||| For a given list and a given index, there is only one possible value
||| stored at that index in that list
export
atIndexUnique : AtIndex k a as -> AtIndex k b as -> a === b
atIndexUnique Z Z = Refl
atIndexUnique (S p) (S q) = atIndexUnique p q

||| Provided that equality is decidable, we can look for the first occurence
||| of a value inside of a list
public export
find : DecEq a => (x : a) -> (xs : List a) -> Dec (Subset Nat (\ n => AtIndex n x xs))
find x [] = No (\ p => void (absurd (snd p)))
find x (y :: xs) with (decEq x y)
  find x (x :: xs) | Yes Refl = Yes (Element Z Z)
  find x (y :: xs) | No neqxy = case find x xs of
      Yes (Element n prf) => Yes (Element (S n) (S prf))
      No notInxs => No \case
        (Element Z p) => void (neqxy (inverseZ p))
        (Element (S n) prf) => absurd (notInxs (Element n (inverseS prf)))

||| If the equality is not decidable, we may instead rely on interface resolution
public export
interface FindElement (0 t : a) (0 ts : List a) where
  findElement : Subset Nat (\ k => AtIndex k t ts)

FindElement t (t :: ts) where
  findElement = Element 0 Z

FindElement t ts => FindElement t (u :: ts) where
  findElement = let (Element n prf) = findElement in
                Element (S n) (S prf)

||| Given an index, we can decide whether there is a value corresponding to it
public export
lookup : (n : Nat) -> (xs : List a) -> Dec (Subset a (\ x => AtIndex n x xs))
lookup n [] = No (\ p => void (absurd (snd p)))
lookup Z (x :: xs) = Yes (Element x Z)
lookup (S n) (x :: xs) = case lookup n xs of
  Yes (Element x p) => Yes (Element x (S p))
  No notInxs => No (\ (Element x p) => void (notInxs (Element x (inverseS p))))

||| An AtIndex proof implies that n is less than the length of the list indexed into
public export
inRange : (n : Nat) -> (xs : List a) -> (0 _ : AtIndex n x xs) -> LTE n (length xs)
inRange n [] p = void (absurd p)
inRange Z (x :: xs) p = LTEZero
inRange (S n) (x :: xs) p = LTESucc (inRange n xs (inverseS p))

|||
export
weakenR : AtIndex n x xs -> AtIndex n x (xs ++ ys)
weakenR Z = Z
weakenR (S p) = S (weakenR p)

export
weakenL : (m : Nat) -> (0 _ : HasLength m ws) -> AtIndex n x xs -> AtIndex (m + n) x (ws ++ xs)
weakenL Z Z p = p
weakenL (S m) (S len) p = S (weakenL m len p)
