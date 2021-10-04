module Data.List.Extra

import Data.List

%default total

||| Enumerate a Vect with indicies of Nat
public export
enumNat : List a -> List (Nat, a)
enumNat l = h 0 l where
  h : Nat -> List a -> List (Nat, a)
  h _ [] = []
  h n (x :: xs) = (n, x) :: h (S n) xs

||| Enumerate a Vect with indicies of Elem
public export
enumElem : (l : List a) -> List (e : a ** Elem e l)
enumElem [] = []
enumElem (x :: xs) = (x ** Here) :: map (\(s ** f) => (s ** There f)) (enumElem xs) 

||| Applied to a predicate and a list, returns the list of those elements that
||| satisfy the predicate with corresponding indices in a stand-alone list.
||| See also `Data.List.Extra.filterLoc'`.
public export
filterLoc : (a -> Bool) -> List a -> (List a, List Nat)
filterLoc p = h 0 where
  h : Nat -> List a -> (List a, List Nat)
  h _ [] = ([], [])
  h lvl (x :: xs) = if p x
      then let (ms, ns) = h (S lvl) xs in (x :: ms, lvl :: ns)
      else h (S lvl) xs

||| Applied to a predicate and a list, returns the list of those elements that
||| satisfy the predicate with corresponding indices.
public export
filterLoc' : (a -> Bool) -> List a -> List (a, Nat)
filterLoc' p = h 0 where
  h : Nat -> List a -> List (a, Nat)
  h _ [] = []
  h lvl (x :: xs) = if p x
    then (x, lvl) :: h (S lvl) xs
    else             h (S lvl) xs
