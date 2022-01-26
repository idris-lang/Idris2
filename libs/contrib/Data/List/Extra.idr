module Data.List.Extra

%default total

||| Analogous to `map` for `List`, but the function is applied to the index of
||| the element as first argument (counting from 0), and the element itself as
||| second argument.
public export
mapi : ((n : Nat) -> (a -> b))
    -> (xs : List a)
    -> List b
mapi = h 0 where
  h : Nat -> ((n : Nat) -> (a -> b))
   -> (xs : List a)
   -> List b
  h i f [] = []
  h i f (x :: xs) = f i x :: h (S i) f xs

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
