module Data.List.Extra

import Data.List

%default total

||| Map with index parameter
|||
||| ```idris example
||| mapI (*) [4,1,2,1]
||| ```
public export
mapI : (Nat -> a -> b) -> List a -> List b
mapI f list = mapI' Z list where
  mapI' : Nat -> List a -> List b
  mapI' _ [] = []
  mapI' i (x::xs) = f i x :: mapI' (S i) xs


||| MapMaybe with index parameter
|||
||| ```idris example
||| mapMaybeI (\i => \x => if i /= x then Just (i * x) else Nothing) [4,1,2,1]
||| ```
public export
mapMaybeI : (Nat -> a -> Maybe b) -> List a -> List b
mapMaybeI f vect = mapMaybeI' Z vect where
  mapMaybeI' : Nat -> List a -> List b
  mapMaybeI' _ []      = []
  mapMaybeI' i (x::xs) =
    case f i x of
    Nothing => mapMaybeI' (S i) xs
    Just j  => j :: mapMaybeI' (S i) xs

||| Filter with index as extra parameter for the predicate
|||
||| ```idris example
||| filterI (==) [4,1,2,1]
||| ```
public export
filterI : (Nat -> a -> Bool) -> List a -> List a
filterI p list = filterI' Z list where
  filterI' : Nat -> List a -> List a
  filterI' _ [] = []
  filterI' i (x :: xs) =
    if p i x
      then x :: filterI' (S i) xs
      else filterI' (S i) xs

||| Foldr with index parameter
|||
||| ```idris example
||| foldrI (\i => \x => (+) (i * x)) 0 [4,1,2,1]
public export
foldrI : (Nat -> elem -> acc -> acc) -> acc -> List elem -> acc
foldrI f z list = let (_, z') = foldrI' list in z' where
  foldrI' : List elem -> (Nat, acc)
  foldrI' [] = (Z, z)
  foldrI' (x :: xs) = let (i, z') = foldrI' xs
                      in (S i, f i x z')

||| Foldl with index parameter
|||
||| ```idris example
||| foldlI (\res => \i => \x => res + i * x) 0 [4,1,2,1]
||| ```
public export
foldlI : (acc -> Nat -> elem -> acc) -> acc -> List elem -> acc
foldlI f z list = foldlI' Z z list where
  foldlI' : Nat -> acc -> List elem -> acc
  foldlI' _ z [] = z
  foldlI' i z (x :: xs) = foldlI' (S i) (f z i x) xs

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
