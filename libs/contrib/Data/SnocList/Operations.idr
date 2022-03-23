||| Operations on `SnocList`s, analogous to the `List` ones.
||| Depending on your style of programming, these might cause
||| ambiguities, so import with care
module Data.SnocList.Operations

import Data.SnocList
import Data.List
import Data.Nat
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

%default total

||| Take `n` last elements from `sx`, returning the whole list if
||| `n` >= length `sx`.
|||
||| @ n  the number of elements to take
||| @ sx the snoc-list to take the elements from
public export
ekat : (n : Nat) -> (sx : SnocList a) -> SnocList a
ekat (S n) (sx :< x) = ekat n sx :< x
ekat _ _ = [<]

||| Remove `n` last elements from `xs`, returning the empty list if
||| `n >= length xs`
|||
||| @ n  the number of elements to remove
||| @ xs the list to drop the elements from
public export
pord : (n : Nat) -> (sx : SnocList a) -> SnocList a
pord  0    sx        = sx
pord (S n) [<]       = [<]
pord (S n) (sx :< x) = pord n sx

public export
concatPordEkat : (n : Nat) -> (sx : SnocList a) ->
  pord n sx ++ ekat n sx === sx
concatPordEkat 0 (sx :< x) = Refl
concatPordEkat (S n) (sx :< x) = cong (:< x) $ concatPordEkat n sx
concatPordEkat 0 [<] = Refl
concatPordEkat (S k) [<] = Refl


{- We can traverse a list while retaining both sides by decomposing it
   into a snoc-list and a cons-list
-}

||| Shift `n` elements from the beginning of `xs` to the end of `sx`,
||| returning the same lists if `n` >= length `xs`.
|||
||| @ n  the number of elements to take
||| @ sx the snoc-list to append onto
||| @ xs the list to take the elements from
public export
splitOntoLeft : (n : Nat) -> (sx : SnocList a) -> (xs : List a) -> (SnocList a, List a)
splitOntoLeft (S n) sx (x :: xs) = splitOntoLeft n (sx :< x) xs
splitOntoLeft _ sx xs = (sx, xs)

||| Shift `n` elements from the end of `sx` to the beginning of `xs`,
||| returning the same lists if `n` >= length `sx`.
|||
||| @ n  the number of elements to take
||| @ sx the snoc-list to take the elements from
||| @ xs the list to append onto
public export
splitOntoRight : (n : Nat) -> (sx : SnocList a) -> (xs : List a) -> (SnocList a, List a)
splitOntoRight (S n) (sx :< x) xs = splitOntoRight n sx (x :: xs)
splitOntoRight _ sx xs = (sx, xs)

export
splitOntoRightInvariant : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  fst (splitOntoRight n sx xs) <>< snd (splitOntoRight n sx xs) === sx <>< xs
splitOntoRightInvariant (S n) (sx :< x) xs = splitOntoRightInvariant n sx (x :: xs)
splitOntoRightInvariant  0    sx  xs = Refl
splitOntoRightInvariant (S k) [<] xs = Refl

export
splitOntoRightSpec : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  (fst (splitOntoRight n sx xs) === pord n sx, snd (splitOntoRight n sx xs) = ekat n sx <>> xs)
splitOntoRightSpec (S k) (sx :< x) xs = splitOntoRightSpec k sx (x :: xs)
splitOntoRightSpec  0    sx        xs = (Refl, Refl)
splitOntoRightSpec (S k) [<]       xs = (Refl, Refl)

export
splitOntoLeftSpec : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  (fst (splitOntoLeft n sx xs) === sx <>< take n xs, snd (splitOntoLeft n sx xs) = drop n xs)
splitOntoLeftSpec (S k) sx (x :: xs) = splitOntoLeftSpec k (sx :< x) xs
splitOntoLeftSpec  0    sx        xs = (Refl, Refl)
splitOntoLeftSpec (S k) sx [] = (Refl, Refl)

export
lengthHomomorphism : (sx,sy : SnocList a) -> length (sx ++ sy) === length sx + length sy
lengthHomomorphism sx [<] = sym $ plusZeroRightNeutral _
lengthHomomorphism sx (sy :< x) = Calc $
  |~ 1 + (length (sx ++ sy))
  ~~ 1 + (length sx + length sy) ...(cong (1+) $ lengthHomomorphism _ _)
  ~~ length sx + (1 + length sy) ...(plusSuccRightSucc _ _)

-- cons-list operations on snoc-lists

||| Take `n` first elements from `sx`, returning the whole list if
||| `n` >= length `sx`.
|||
||| @ n  the number of elements to take
||| @ sx the snoc-list to take the elements from
|||
||| Note: traverses the whole the input list, so linear in `n` and
||| `length sx`
public export
take : (n : Nat) -> (sx : SnocList a) -> SnocList a
take n sx = pord (length sx `minus` n) sx

||| Drop `n` first elements from `sx`, returning an empty list if
||| `n` >= length `sx`.
|||
||| @ n  the number of elements to drop
||| @ sx the snoc-list to drop the elements from
|||
||| Note: traverses the whole the input list, so linear in `n` and
||| `length sx`
public export
drop : (n : Nat) -> (sx : SnocList a) -> SnocList a
drop n sx = ekat (length sx `minus` n) sx

public export
data NonEmpty : SnocList a -> Type where
  IsSnoc : NonEmpty (sx :< x)

public export
last : (sx : SnocList a) -> {auto 0 nonEmpty : NonEmpty sx} -> a
last (sx :< x) {nonEmpty = IsSnoc} = x

public export
intersectBy : (a -> a -> Bool) -> SnocList a -> SnocList a -> SnocList a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

public export
intersect : Eq a => SnocList a -> SnocList a -> SnocList a
intersect = intersectBy (==)
