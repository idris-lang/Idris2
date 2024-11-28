-- Remove as soon as 0.8.0 (or greater) is released
module Libraries.Data.SortedSet

import Data.Maybe
import Libraries.Data.SortedMap

%default total

export
data SortedSet k = SetWrapper (Data.SortedMap.SortedMap k ())

export
empty : Ord k => SortedSet k
empty = SetWrapper Data.SortedMap.empty

export
insert : k -> SortedSet k -> SortedSet k
insert k (SetWrapper m) = SetWrapper (Data.SortedMap.insert k () m)

export
delete : k -> SortedSet k -> SortedSet k
delete k (SetWrapper m) = SetWrapper (Data.SortedMap.delete k m)

export
contains : k -> SortedSet k -> Bool
contains k (SetWrapper m) = isJust (Data.SortedMap.lookup k m)

export
fromList : Ord k => List k -> SortedSet k
fromList l = SetWrapper (Data.SortedMap.fromList (map (\i => (i, ())) l))

export
Foldable SortedSet where
  foldr f z = foldr f z . toList
  foldl f z = foldl f z . toList

  null (SetWrapper m) = null m

  foldMap f = foldMap f . toList

  toList (SetWrapper m) = Data.SortedMap.keys m

||| use `Prelude.toList`
%deprecate
export %inline
toList : SortedSet k -> List k
toList = Prelude.toList

||| Set union. Inserts all elements of x into y
export
union : (x, y : SortedSet k) -> SortedSet k
union x y = foldr insert x y

||| Set difference. Delete all elments in y from x
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

export
keySet : SortedMap k v -> SortedSet k
keySet = SetWrapper . map (const ())

export
differenceMap : SortedMap k v -> SortedSet k -> SortedMap k v
differenceMap x y = foldr delete x y

export
intersectionMap : SortedMap k v -> SortedSet k -> SortedMap k v
intersectionMap x y = differenceMap x (keySet $ differenceMap x y)

export
Ord k => Semigroup (SortedSet k) where
  (<+>) = union

export
Ord k => Monoid (SortedSet k) where
  neutral = empty

export
Show k => Show (SortedSet k) where
  show = show . Prelude.toList

export
singleton : Ord k => k -> SortedSet k
singleton k = insert k empty

export
toSortedMap : SortedSet k -> SortedMap k ()
toSortedMap (SetWrapper m) = m

||| Returns the leftmost (least) value
export
leftMost : SortedSet k -> Maybe k
leftMost (SetWrapper m) = fst <$> leftMost m

export
pop : SortedSet k -> Maybe (k, SortedSet k)
pop (SetWrapper m) = do
  ((k, ()), m) <- pop m
  pure (k, SetWrapper m)
