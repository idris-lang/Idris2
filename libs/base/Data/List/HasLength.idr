||| This module implements a relation between a natural number and a list.
||| The relation witnesses the fact the number is the length of the list.
|||
||| It is meant to be used in a runtime-irrelevant fashion in computations
||| manipulating data indexed over lists where the computation actually only
||| depends on the length of said lists.
|||
||| Instead of writing:
||| ```idris example
||| f0 : (xs : List a) -> P xs
||| ```
|||
||| We would write either of:
||| ```idris example
||| f1 : (n : Nat) -> (0 _ : HasLength n xs) -> P xs
||| f2 : (n : Subset n (flip HasLength xs)) -> P xs
||| ```
|||
||| See `sucR` for an example where the update to the runtime-relevant Nat is O(1)
||| but the udpate to the list (were we to keep it around) an O(n) traversal.

module Data.List.HasLength

import Data.DPair
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- Type

||| Ensure that the list's length is the provided natural number
public export
data HasLength : Nat -> List a -> Type where
  Z : HasLength Z []
  S : HasLength n xs -> HasLength (S n) (x :: xs)

||| This specification corresponds to the length function
export
hasLength : (xs : List a) -> HasLength (length xs) xs
hasLength [] = Z
hasLength (_ :: xs) = S (hasLength xs)

export
take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
take Z _ = Z
take (S n) (x :: xs) = S (take n xs)

------------------------------------------------------------------------
-- Properties

||| The length is unique
export
hasLengthUnique : HasLength m xs -> HasLength n xs -> m === n
hasLengthUnique Z Z = Refl
hasLengthUnique (S p) (S q) = cong S (hasLengthUnique p q)

export
hasLengthAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (xs ++ ys)
hasLengthAppend Z ys = ys
hasLengthAppend (S xs) ys = S (hasLengthAppend xs ys)

hasLengthReverseOnto : HasLength m acc -> HasLength n xs -> HasLength (m + n) (reverseOnto acc xs)
hasLengthReverseOnto p Z = rewrite plusZeroRightNeutral m in p
hasLengthReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hasLengthReverseOnto (S p) q

export
hasLengthReverse : HasLength m acc -> HasLength m (reverse acc)
hasLengthReverse = hasLengthReverseOnto Z

export
map : (f : a -> b) -> HasLength n xs -> HasLength n (map f xs)
map f Z = Z
map f (S n) = S (map f n)

||| @sucR demonstrates that snoc only increases the lenght by one
||| So performing this operation while carrying the list around would cost O(n)
||| but relying on n together with an erased HasLength proof instead is O(1)
export
sucR : HasLength n xs -> HasLength (S n) (snoc xs x)
sucR Z = S Z
sucR (S n) = S (sucR n)

------------------------------------------------------------------------
-- Views

namespace SubsetView

  ||| We provide this view as a convenient way to perform nested pattern-matching
  ||| on values of type `Subset Nat (flip HasLength xs)`. Functions using this view will
  ||| be seen as terminating as long as the index list `xs` is left untouched.
  ||| See e.g. listTerminating below for such a function.
  public export
  data View : (xs : List a) -> Subset Nat (flip HasLength xs) -> Type where
    Z : View [] (Element Z Z)
    S : (p : Subset Nat (flip HasLength xs)) -> View (x :: xs) (Element (S (fst p)) (S (snd p)))

  ||| This auxiliary function gets around the limitation of the check ensuring that
  ||| we do not match on runtime-irrelevant data to produce runtime-relevant data.
  viewZ : (0 p : HasLength Z xs) -> View xs (Element Z p)
  viewZ Z = Z

  ||| This auxiliary function gets around the limitation of the check ensuring that
  ||| we do not match on runtime-irrelevant data to produce runtime-relevant data.
  viewS : (n : Nat) -> (0 p : HasLength (S n) xs) -> View xs (Element (S n) p)
  viewS n (S p) = S (Element n p)

  ||| Proof that the view covers all possible cases.
  export
  view : (p : Subset Nat (flip HasLength xs)) -> View xs p
  view (Element Z p) = viewZ p
  view (Element (S n) p) = viewS n p

namespace CurriedView

  ||| We provide this view as a convenient way to perform nested pattern-matching
  ||| on pairs of values of type `n : Nat` and `HasLength xs n`. If transformations
  ||| to the list between recursive calls (e.g. mapping over the list) that prevent
  ||| it from being a valid termination metric, it is best to take the Nat argument
  ||| separately from the HasLength proof and the Subset view is not as useful anymore.
  ||| See e.g. natTerminating below for (a contrived example of) such a function.
  public export
  data View : (xs : List a) -> (n : Nat) -> HasLength n xs -> Type where
    Z : View [] Z Z
    S : (n : Nat) -> (0 p : HasLength n xs) -> View (x :: xs) (S n) (S p)

  ||| Proof that the view covers all possible cases.
  export
  view : (n : Nat) -> (0 p : HasLength n xs) -> View xs n p
  view Z Z = Z
  view (S n) (S p) = S n p

------------------------------------------------------------------------
-- Examples

-- /!\ Do NOT re-export these examples

listTerminating : (p : Subset Nat (flip HasLength xs)) -> HasLength (S (fst p)) (xs ++ [x])
listTerminating p with (view p)
  listTerminating (Element 0 Z) | Z = S Z
  listTerminating (Element (S (fst y)) (S (snd y))) | (S y) = S (listTerminating y)

data P : List Nat -> Type where
  PNil : P []
  PCon : P (map f xs) -> P (x :: xs)

covering
notListTerminating : (p : Subset Nat (flip HasLength xs)) -> P xs
notListTerminating p with (view p)
  notListTerminating (Element 0 Z) | Z = PNil
  notListTerminating (Element (S (fst y)) (S (snd y))) | (S y) =
    PCon (notListTerminating {xs = map id (tail xs)} ({ snd $= map id } y))

natTerminating : (n : Nat) -> (0 p : HasLength n xs ) -> P xs
natTerminating n p = case view n p of
  Z => PNil
  S n p => PCon (natTerminating n (map id p))

