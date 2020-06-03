||| Properties of the reverse function.
module Data.List.Reverse

import Data.Nat
import Data.List
import Data.List.Equalities

%default total

export
reverseOntoAcc : (xs, ys, zs : List a) ->
  reverseOnto (ys ++ zs) xs = (reverseOnto ys xs) ++ zs
reverseOntoAcc [] _ _ = Refl
reverseOntoAcc (x :: xs) (ys) (zs) = reverseOntoAcc xs (x :: ys) zs

||| Serves as a specification for reverseOnto.
export
reverseOntoSpec : (xs, ys : List a) -> reverseOnto xs ys = reverse ys ++ xs
reverseOntoSpec xs ys = reverseOntoAcc ys [] xs

||| The reverse of an empty list is an empty list.  Together with reverseCons,
||| serves as a specification for reverse.
export
reverseNil : reverse [] = []
reverseNil = Refl

||| The reverse of a cons is the reverse of the tail followed by the head.
||| Together with reverseNil serves as a specification for reverse.
export
reverseCons : (x : a) -> (xs : List a) -> reverse (x::xs) = reverse xs `snoc` x
reverseCons x xs = reverseOntoSpec [x] xs

||| Reversing an append is appending reversals backwards.
export
reverseAppend : (xs, ys : List a) ->
  reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseAppend [] ys = sym (appendNilRightNeutral (reverse ys))
reverseAppend (x :: xs) ys =
  rewrite reverseCons x (xs ++ ys) in
    rewrite reverseAppend xs ys in
      rewrite reverseCons x xs in
        sym $ appendAssociative (reverse ys) (reverse xs) [x]

||| A slow recursive definition of reverse.
public export
0 slowReverse : List a -> List a
slowReverse [] = []
slowReverse (x :: xs) = slowReverse xs `snoc` x

||| The iterative and recursive defintions of reverse are the same.
export
reverseEquiv : (xs : List a) -> slowReverse xs = reverse xs
reverseEquiv [] = Refl
reverseEquiv (x :: xs) =
  rewrite reverseEquiv xs in
    rewrite reverseAppend [x] xs in
      Refl

||| Reversing a singleton list is a no-op.
export
reverseSingletonId : (x : a) -> reverse [x] = [x]
reverseSingletonId _ = Refl

||| Reversing a reverse gives the original.
export
reverseReverseId : (xs : List a) -> reverse (reverse xs) = xs
reverseReverseId [] = Refl
reverseReverseId (x :: xs) =
  rewrite reverseCons x xs in
    rewrite reverseAppend (reverse xs) [x] in
      rewrite reverseReverseId xs in
        Refl

||| Reversing onto preserves list length.
export
reverseOntoLength : (xs, acc : List a) ->
  length (reverseOnto acc xs) = length acc + length xs
reverseOntoLength [] acc = rewrite plusZeroRightNeutral (length acc) in Refl
reverseOntoLength (x :: xs) acc =
  rewrite reverseOntoLength xs (x :: acc) in
    plusSuccRightSucc (length acc) (length xs)

||| Reversing preserves list length.
export
reverseLength : (xs : List a) -> length (reverse xs) = length xs
reverseLength xs = reverseOntoLength xs []

||| Equal reversed lists are equal.
export
reverseEqual : (xs, ys : List a) -> reverse xs = reverse ys -> xs = ys
reverseEqual xs ys prf =
  rewrite sym $ reverseReverseId xs in
    rewrite prf in
      reverseReverseId ys
