module Data.List.IsSublist

import Control.Relation
import Data.List

public export
data IsSublist : List a -> List a -> Type where
    Base : IsSublist [] []
    Skip : IsSublist xs ys -> IsSublist xs (y :: ys)
    Keep : IsSublist xs ys -> IsSublist (x :: xs) (x :: ys)

public export
weakenSublist : IsSublist (y :: ys) xs -> IsSublist ys xs
weakenSublist (Skip sublist) = Skip $ weakenSublist sublist
weakenSublist (Keep sublist) = Skip sublist

export
Uninhabited (IsSublist (x :: ys) ys) where
  uninhabited Base impossible
  uninhabited (Skip sublist) = uninhabited (weakenSublist sublist)
  uninhabited (Keep sublist) = uninhabited sublist

export
Uninhabited (IsSublist xs ys) => Uninhabited (IsSublist (z :: xs) (z :: ys)) where
  uninhabited Base impossible
  uninhabited (Skip sublist) = uninhabited $ weakenSublist sublist
  uninhabited (Keep sublist) = uninhabited sublist

public export
Reflexive (List a) IsSublist where
  reflexive {x = []} = Base
  reflexive {x = y :: ys} = Keep reflexive

nilSublist : {xs : List a} -> IsSublist [] xs
nilSublist {xs = []} = Base
nilSublist {xs = y :: xs} = Skip nilSublist

public export
Transitive (List a) IsSublist where
  transitive sublist Base = sublist
  transitive sublist (Skip sublist1) = Skip $ transitive sublist sublist1
  transitive (Skip sublist1) (Keep sublist2) = Skip $ transitive sublist1 sublist2
  transitive (Keep sublist1) (Keep sublist2) = Keep $ transitive sublist1 sublist2

sublistSwapAppend : {ys1, ys2 : List a} -> {y : a} -> IsSublist ys1 ys2  -> IsSublist (y :: ys2) ys1 -> Void
sublistSwapAppend (Skip sublist1) sublist2 = uninhabited $ weakenSublist $ transitive sublist2 sublist1
sublistSwapAppend (Keep sublist1) (Keep sublist2) = uninhabited $ transitive sublist2 sublist1
sublistSwapAppend (Keep sublist1) (Skip sublist2) = uninhabited $ weakenSublist $ transitive sublist2 sublist1
sublistSwapAppend Base sublist2 = uninhabited sublist2

export
{ys1, ys2 : List a} -> {y : a} -> IsSublist ys1 ys2  => Uninhabited (IsSublist (y :: ys2) ys1) where
  uninhabited @{sublist1} sublist2 = void $ sublistSwapAppend sublist1 sublist2

public export
Antisymmetric (List a) IsSublist where
  antisymmetric Base Base = Refl
  antisymmetric (Keep {x} sublist1) (Keep sublist2) =
    cong ((::) x) $ antisymmetric sublist1 sublist2
  antisymmetric (Keep {x} sublist1) (Skip sublist2) =
    let rec = antisymmetric sublist1 $ weakenSublist sublist2 in cong ((::) x) rec
  antisymmetric (Skip sublist1) sublist2 =
    absurd $ uninhabited sublist2

public export
removeSublist : {ys : List a} -> IsSublist xs ys -> List a
removeSublist Base = []
removeSublist (Skip {y} rest) = y :: removeSublist rest
removeSublist (Keep rest) = removeSublist rest

public export
filterSublist : {ys : List a} -> {p : a -> Bool} -> IsSublist (filter p ys) ys
filterSublist {ys = []} = Base
filterSublist {ys = y :: ys} with (p y)
  filterSublist {ys = y :: ys} | True = Keep filterSublist
  filterSublist {ys = y :: ys} | False = Skip filterSublist

public export
takeSublist : {ys : List a} -> {n : Nat} -> IsSublist (take n ys) ys
takeSublist {ys = y :: ys} {n = S k} = Keep takeSublist
takeSublist {ys = y :: ys} {n = Z} = nilSublist
takeSublist {ys = []} {n = S k} = Base
takeSublist {ys = []} {n = Z} = Base

public export
dropSublist : {ys : List a} -> {n : Nat} -> IsSublist (drop n ys) ys
dropSublist {ys = y :: ys} {n = S k} = Skip dropSublist
dropSublist {ys = y :: ys} {n = Z} = reflexive
dropSublist {ys = []} {n = S k} = Base
dropSublist {ys = []} {n = Z} = Base
