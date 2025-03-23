module Data.SortedSet

import Data.Maybe
import Data.SortedMap
import Data.SortedMap.Dependent

export
data SortedSet k = SetWrapper (Data.SortedMap.SortedMap k ())

export
empty : Ord k => SortedSet k
empty = SetWrapper Data.SortedMap.empty

export
insert : k -> SortedSet k -> SortedSet k
insert k (SetWrapper m) = SetWrapper (Data.SortedMap.insert k () m)

public export %inline
insert' : SortedSet k -> k -> SortedSet k
insert' = flip insert

export
delete : k -> SortedSet k -> SortedSet k
delete k (SetWrapper m) = SetWrapper (Data.SortedMap.delete k m)

public export %inline
delete' : SortedSet k -> k -> SortedSet k
delete' = flip delete

export
contains : k -> SortedSet k -> Bool
contains k (SetWrapper m) = isJust (Data.SortedMap.lookup k m)

public export %inline
contains' : SortedSet k -> k -> Bool
contains' = flip contains

export
fromList : Ord k => List k -> SortedSet k
fromList l = SetWrapper (Data.SortedMap.fromList (map (\i => (i, ())) l))

export
Foldable SortedSet where
  foldr f z = foldr f z . toList
  foldl f z = foldl f z . toList

  null (SetWrapper m) = null m

  foldMap f = foldMap f . toList

  toList (SetWrapper m) = keys m

-- Remove as soon as 0.8.0 (or greater) is released
||| Use `Prelude.toList` instead
%deprecate
public export %inline
toList : SortedSet k -> List k
toList = Prelude.toList

||| Set union. Inserts all elements of x into y
export
union : (x, y : SortedSet k) -> SortedSet k
union x y = foldr insert x y

||| Set difference. Delete all elements in y from x
export
difference : (x, y : SortedSet k) -> SortedSet k
difference x y = foldr delete x y

||| Set symmetric difference. Uses the union of the differences.
export
symDifference : (x, y : SortedSet k) -> SortedSet k
symDifference x y = union (difference x y) (difference y x)

||| Set intersection. Implemented as the difference of the union and the symetric difference.
export
intersection : (x, y : SortedSet k) -> SortedSet k
intersection x y = difference x (difference x y)

||| Returns the leftmost (least) value
export
leftMost : SortedSet k -> Maybe k
leftMost (SetWrapper m) = fst <$> leftMost m

||| Returns the rightmost (greatest) value
export
rightMost : SortedSet k -> Maybe k
rightMost (SetWrapper m) = fst <$> rightMost m

export
Ord k => Semigroup (SortedSet k) where
  (<+>) = union

export
Ord k => Monoid (SortedSet k) where
  neutral = empty

export
Eq k => Eq (SortedSet k) where
  SetWrapper x == SetWrapper y = x == y

export
Show k => Show (SortedSet k) where
   show m = "fromList " ++ show (Prelude.toList m)

export
keySet : SortedMap k v -> SortedSet k
keySet = SetWrapper . map (const ())

namespace Dependent

  export
  keySet : SortedDMap k v -> SortedSet k
  keySet = SetWrapper . cast . map (const ())

||| Removes all given keys from the given map
export
differenceMap : SortedMap k v -> SortedSet k -> SortedMap k v
differenceMap x y = foldr delete x y

||| Leaves only given keys in the given map
export
intersectionMap : SortedMap k v -> SortedSet k -> SortedMap k v
intersectionMap x y = differenceMap x (keySet $ differenceMap x y)

export
singleton : Ord k => k -> SortedSet k
singleton = insert' empty

export %inline
toSortedMap : SortedSet k -> SortedMap k ()
toSortedMap (SetWrapper m) = m

export %inline
fromSortedMap : SortedMap k () -> SortedSet k
fromSortedMap = SetWrapper

||| Pops the leftmost element from the set
export
pop : SortedSet k -> Maybe (k, SortedSet k)
pop (SetWrapper m) = bimap fst fromSortedMap <$> pop m
