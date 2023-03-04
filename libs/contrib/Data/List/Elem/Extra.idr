module Data.List.Elem.Extra

import Data.List
import Data.List.Elem
import Data.List.AtIndex
import Control.Relation

%default total

||| Proof that an element is still inside a list if we append to it.
public export
elemAppLeft : (xs, ys : List a) -> (prf : Elem x xs) -> Elem x (xs ++ ys)
elemAppLeft (x :: xs) ys Here = Here
elemAppLeft (x :: xs) ys (There prf2) = There $ elemAppLeft xs ys prf2


||| Proof that an element is still inside a list if we prepend to it.
public export
elemAppRight :  (ys, xs : List a) -> (prf : Elem x xs) -> Elem x (ys ++ xs)
elemAppRight [] xs prf = prf
elemAppRight (y :: ys) xs prf = There $ elemAppRight ys xs prf

||| Proof that membership on append implies membership in left or right sublist.
public export
elemAppLorR : (xs, ys : List a)
           -> (prf : Elem k (xs ++ ys))
           -> Either (Elem k xs) (Elem k ys)
elemAppLorR [] [] prf = absurd prf
elemAppLorR [] _ prf = Right prf
elemAppLorR (x :: xs) [] prf =
  Left $ rewrite sym $ appendNilRightNeutral xs in prf
elemAppLorR (x :: xs) _ Here = Left Here
elemAppLorR (x :: xs) ys (There prf) = mapFst There $ elemAppLorR xs ys prf


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

||| Convert Elem to AtIndex.
public export
elemAtIndex : Elem x xs  -> (n ** AtIndex x xs n)
elemAtIndex Here = (Z ** Z)
elemAtIndex (There later) = 
  let (n ** atIndex) = elemAtIndex later in (S n ** S atIndex)

public export
data IsSublist : List a -> List a -> Type where
    Base : IsSublist [] []
    Skip : (y : a) -> IsSublist xs ys -> IsSublist xs (y :: ys)
    Keep : (x : a) -> (el : Elem x xs) -> IsSublist (dropElem xs el) ys -> IsSublist xs (x :: ys)

public export
dropSublist : {0 xs, ys : List a} -> IsSublist xs ys -> List a
dropSublist Base = []
dropSublist (Skip y rest) = y :: dropSublist rest
dropSublist (Keep _ _ rest) = dropSublist rest

public export
nilSublist : {xs : List a} -> IsSublist [] xs
nilSublist {xs = []} = Base
nilSublist {xs = y :: xs} = Skip y nilSublist

tailSublist : IsSublist (y :: ys) xs -> IsSublist ys xs
tailSublist (Skip y sublist) = Skip y $ tailSublist sublist
tailSublist (Keep z Here sublist) =  Skip z sublist
tailSublist (Keep z (There later) sublist) = Keep z later $ tailSublist sublist

{el : Elem z (x :: (z :: ys))} -> Uninhabited (IsSublist (dropElem (x :: (z :: ys)) el) ys) where
  uninhabited {el = Here} (Skip y sublist) = ?uninhabited_rhs1
  uninhabited {el = Here} (Keep z el sublist) = ?uninhabited_rhs2
  uninhabited {el = There el} sublist = ?uninhabited_rhs3

Uninhabited (IsSublist (x :: ys) ys) where
  uninhabited Base impossible
  uninhabited (Skip y sublist) = uninhabited (tailSublist sublist)
  uninhabited (Keep z (Here {x = z}) sublist) = uninhabited sublist
  uninhabited (Keep z el sublist) = ?uninhabited_rhs

Reflexive (List a) IsSublist where
  reflexive {x = []} = Base 
  reflexive {x = y :: ys} = Keep y Here reflexive

Transitive (List a) IsSublist where
  transitive sublist Base = sublist
  transitive sublist (Skip y sublist1) = Skip y $ transitive sublist sublist1
  transitive (Skip x sublist1) (Keep x Here sublist2) = Skip x $ transitive sublist1 sublist2
  transitive (Skip z sublist1) (Keep y el sublist2) = ?as2
  transitive (Keep y el1 sublist1) (Keep z el2 sublist2) = ?as1
  transitive (Keep y (There el1) sublist1) (Keep z (There el2) sublist2) = ?transitive_rhs
