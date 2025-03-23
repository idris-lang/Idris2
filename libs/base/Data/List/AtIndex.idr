||| Indexing into Lists.
|||
||| `Elem` proofs give existential quantification that a given element
||| *is* in the list, but not where in the list it is!  Here we give a
||| predicate that presents proof that a given index in a list, given
||| by a natural number, will return a certain element.

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
data AtIndex : a -> List a -> Nat -> Type where
  Z : AtIndex a (a :: as) Z
  S : AtIndex a as n -> AtIndex a (b :: as) (S n)

||| Inversion principle for Z constructor
export
inverseZ : AtIndex x (y :: xs) Z -> x === y
inverseZ Z = Refl

||| inversion principle for S constructor
export
inverseS : AtIndex x (y :: xs) (S n) -> AtIndex x xs n
inverseS (S p) = p

||| An empty list cannot possibly have members
export
Uninhabited (AtIndex a [] n) where
  uninhabited Z impossible
  uninhabited (S _) impossible

||| For a given list and a given index, there is only one possible value
||| stored at that index in that list
export
atIndexUnique : AtIndex a as n -> AtIndex b as n -> a === b
atIndexUnique Z Z = Refl
atIndexUnique (S p) (S q) = atIndexUnique p q

||| Provided that equality is decidable, we can look for the first occurrence
||| of a value inside of a list
public export
find : DecEq a => (x : a) -> (xs : List a) -> Dec (Subset Nat (AtIndex x xs))
find x [] = No (\ p => void (absurd (snd p)))
find x (y :: xs) with (decEq x y)
  find x (x :: xs) | Yes Refl = Yes (Element Z Z)
  find x (y :: xs) | No neqxy = case find x xs of
      Yes (Element n prf) => Yes (Element (S n) (S prf))
      No notInxs => No $ \case
        (Element Z p) => void (neqxy (inverseZ p))
        (Element (S n) prf) => absurd (notInxs (Element n (inverseS prf)))

||| Given an index, we can decide whether there is a value corresponding to it
public export
lookup : (n : Nat) -> (xs : List a) -> Dec (Subset a (\ x => AtIndex x xs n))
lookup n [] = No (\ p => void (absurd (snd p)))
lookup Z (x :: xs) = Yes (Element x Z)
lookup (S n) (x :: xs) = case lookup n xs of
  Yes (Element x p) => Yes (Element x (S p))
  No notInxs => No (\ (Element x p) => void (notInxs (Element x (inverseS p))))

||| An AtIndex proof implies that n is less than the length of the list indexed into
public export
inRange : (n : Nat) -> (xs : List a) -> (0 _ : AtIndex x xs n) -> LTE n (length xs)
inRange n [] p = void (absurd p)
inRange Z (x :: xs) p = LTEZero
inRange (S n) (x :: xs) p = LTESucc (inRange n xs (inverseS p))

||| An index remains unchanged if we extend the list to the right
export
weakenR : AtIndex x xs n -> AtIndex x (xs ++ ys) n
weakenR Z = Z
weakenR (S p) = S (weakenR p)

||| An index into `xs` is shifted by `m` if we prepend a list of size `m`
||| in front of it
export
weakenL : (p : Subset Nat (flip HasLength ws)) -> AtIndex x xs n -> AtIndex x (ws ++ xs) (fst p + n)
weakenL m p with (view m)
  weakenL (Element 0 Z) p | Z = p
  weakenL (Element (S (fst m)) (S (snd m))) p | (S m) = S (weakenL m p)

||| Conversely to `weakenR`, if an index is smaller than the length of
||| a prefix then it points into that prefix.
export
strengthenL : (p : Subset Nat (flip HasLength xs)) ->
              lt n (fst p) === True ->
              AtIndex x (xs ++ ys) n -> AtIndex x xs n
strengthenL m lt idx with (view m)
  strengthenL (Element (S (fst m)) (S (snd m))) lt Z | (S m) = Z
  strengthenL (Element (S (fst m)) (S (snd m))) lt (S k) | (S m) = S (strengthenL m lt k)

||| Conversely to `weakenL`, if an index is larger than the length of
||| a prefix then it points into the suffix.
export
strengthenR : (p : Subset Nat (flip HasLength ws)) ->
              lte (fst p) n === True ->
              AtIndex x (ws ++ xs) n -> AtIndex x xs (minus n (fst p))
strengthenR m lt idx with (view m)
  strengthenR (Element 0 Z) lt idx | Z = rewrite minusZeroRight n in idx
  strengthenR (Element (S (fst m)) (S (snd m))) lt (S k) | (S m) = strengthenR m lt k
