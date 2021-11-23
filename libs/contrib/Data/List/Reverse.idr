||| Properties of the reverse function.
module Data.List.Reverse

import Data.Nat
import Data.List

-- Additional properties coming out of base's Data.List
--  - revAppend (i.e. reverse xs ++ reverse ys = reverse (ys ++ xs)
--  - reverseInvolutive (i.e. reverse (reverse xs) = xs)

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
    rewrite revAppend [x] xs in
      Refl

||| Reversing a singleton list is a no-op.
export
reverseSingletonId : (x : a) -> reverse [x] = [x]
reverseSingletonId _ = Refl

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
  rewrite sym $ reverseInvolutive xs in
    rewrite prf in
      reverseInvolutive ys
