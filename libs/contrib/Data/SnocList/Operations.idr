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
shiftLeft : (n : Nat) -> (sx : SnocList a) -> (xs : List a) -> (SnocList a, List a)
shiftLeft (S n) sx (x :: xs) = shiftLeft n (sx :< x) xs
shiftLeft _ sx xs = (sx, xs)

||| Shift `n` elements from the end of `sx` to the beginning of `xs`,
||| returning the same lists if `n` >= length `sx`.
|||
||| @ n  the number of elements to take
||| @ sx the snoc-list to take the elements from
||| @ xs the list to append onto
public export
shiftRight : (n : Nat) -> (sx : SnocList a) -> (xs : List a) -> (SnocList a, List a)
shiftRight (S n) (sx :< x) xs = shiftRight n sx (x :: xs)
shiftRight _ sx xs = (sx, xs)

export
shiftRightInvariant : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  fst (shiftRight n sx xs) <>< snd (shiftRight n sx xs) === sx <>< xs
shiftRightInvariant (S n) (sx :< x) xs = shiftRightInvariant n sx (x :: xs)
shiftRightInvariant  0    sx  xs = Refl
shiftRightInvariant (S k) [<] xs = Refl

export
shiftRightSpec : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  (fst (shiftRight n sx xs) === pord n sx, snd (shiftRight n sx xs) = ekat n sx <>> xs)
shiftRightSpec (S k) (sx :< x) xs = shiftRightSpec k sx (x :: xs)
shiftRightSpec  0    sx        xs = (Refl, Refl)
shiftRightSpec (S k) [<]       xs = (Refl, Refl)

export
shiftLeftSpec : (n : Nat) -> (sx : SnocList a) -> (xs : List a) ->
  (fst (shiftLeft n sx xs) === sx <>< take n xs, snd (shiftLeft n sx xs) = drop n xs)
shiftLeftSpec (S k) sx (x :: xs) = shiftLeftSpec k (sx :< x) xs
shiftLeftSpec  0    sx        xs = (Refl, Refl)
shiftLeftSpec (S k) sx [] = (Refl, Refl)

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
public export
take : (n : Nat) -> (sx : SnocList a) -> SnocList a
take n sx = pord (length sx `minus` n) sx

||| Drop `n` first elements from `sx`, returning an empty list if
||| `n` >= length `sx`.
|||
||| @ n  the number of elements to drop
||| @ sx the snoc-list to drop the elements from
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
