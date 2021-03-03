module Data.Elem.Extra

import Data.List
import Data.List.Elem

%default total

||| Convenience lemma showing that prepending nil to xs is just xs.
public export
appendNilLeftNeutral : (xs : List a) -> ([] ++ xs) = xs
appendNilLeftNeutral [] = Refl
appendNilLeftNeutral (x :: xs) = Refl


||| Proof that an element is still inside a list if we append to it.
public export
elemAppLeft : (xs, ys : List a) -> (prf : Elem x xs) -> Elem x (xs ++ ys)
elemAppLeft (x :: xs) ys Here = Here
elemAppLeft (x :: xs) ys (There prf2) = There $ elemAppLeft xs ys prf2


||| Proof that an element is still inside a list if we prepend to it.
public export
elemAppRight :  (xs, ys : List a) -> (prf : Elem x xs) -> Elem x (ys ++ xs)
elemAppRight (x :: xs) [] Here = Here
elemAppRight (x :: xs) [] (There prf2) = There prf2
elemAppRight xs [] prf = prf
elemAppRight xs (y :: ys) prf = There $ elemAppRight xs ys prf

||| Proof that membership on append implies membership in left or right sublist.
public export
elemAppLorR : (xs, ys : List a)
           -> (prf : Elem k (xs ++ ys))
           -> Either (Elem k xs) (Elem k ys)
elemAppLorR [] [] prf = absurd prf
elemAppLorR [] _ prf = Right prf
elemAppLorR (x :: xs) [] prf =
  let eq   : (xs ++ [] = xs)  = appendNilRightNeutral xs
      prf' : Elem k (x :: xs) = replace {p = \g => Elem k (x :: g)} eq prf
  in Left prf'
elemAppLorR (x :: xs) _ Here = Left Here
elemAppLorR (x :: xs) ys (There prf) =
  let iH : Either (Elem k xs) (Elem k ys) = elemAppLorR xs ys prf
  in case iH of
      (Left l) => Left $ There l
      (Right r) => Right r


||| Proof that x is not in (xs ++ ys) implies proof that x is not in xs.
public export
notElemAppLeft : (xs, ys : List a)
              -> (prf : Not (Elem x (xs ++ ys)))
              -> Not (Elem x xs)
notElemAppLeft xs ys prf val = prf $ elemAppLeft xs ys val

||| Proof that x is not in (xs ++ ys) implies proof that x is not in ys.
public export
notElemAppRight : (xs, ys : List a)
               -> (prf : Not (Elem x (xs ++ ys)))
               -> Not (Elem x ys)
notElemAppRight xs ys prf val = prf $ elemAppRight ys xs val
