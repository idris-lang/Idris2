module Data.List.Elem.Extra

import Data.List
import Data.List.Elem

%default total

||| Proof that an element is still inside a list if we append to it.
public export
elemAppLeft : (xs, ys : List a) -> (prf : Elem x xs) -> Elem x (xs ++ ys)
elemAppLeft (x :: xs) ys Here = rewrite consAppend x xs ys in Here
elemAppLeft (x :: xs) ys (There prf2)
  = rewrite consAppend x xs ys in
      There $ elemAppLeft xs ys prf2


||| Proof that an element is still inside a list if we prepend to it.
public export
elemAppRight :  (ys, xs : List a) -> (prf : Elem x xs) -> Elem x (ys ++ xs)
elemAppRight [] xs prf = prf
elemAppRight (y :: ys) xs prf
  = rewrite consAppend y ys xs in
      There $ elemAppRight ys xs prf

||| Proof that membership on append implies membership in left or right sublist.
public export
elemAppLorR : (xs, ys : List a)
           -> (prf : Elem k (xs ++ ys))
           -> Either (Elem k xs) (Elem k ys)
elemAppLorR [] [] prf = absurd prf
elemAppLorR [] _ prf = Right prf
elemAppLorR (x :: xs) [] prf
  = Left $ rewrite sym $ appendNilRightNeutral (x :: xs) in prf
elemAppLorR (x :: xs) ys prf
  = case replace {p = \ t => Elem k t} (consAppend x xs ys) prf of
      Here => Left Here
      (There prf) => mapFst There $ elemAppLorR xs ys prf


||| Proof that x is not in (xs ++ ys) implies proof that x is not in xs.
public export
notElemAppLeft : (xs, ys : List a)
              -> (prf : Not (Elem x (xs ++ ys)))
              -> Not (Elem x xs)
notElemAppLeft xs ys prf = prf . elemAppLeft xs ys

||| Proof that x is not in (xs ++ ys) implies proof that x is not in ys.
public export
notElemAppRight : (ys, xs : List a)
               -> (prf : Not (Elem x (xs ++ ys)))
               -> Not (Elem x ys)
notElemAppRight ys xs prf = prf . elemAppRight xs ys
