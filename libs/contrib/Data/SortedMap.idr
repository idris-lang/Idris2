module Data.SortedMap

import Data.SortedMap.Dependent

%hide Prelude.toList

export
record SortedMap k v where
  constructor M
  unM : SortedDMap k $ const v

-- Helper function
unDPair : (x : a ** const b x) -> (a, b)
unDPair (k ** v) = (k, v)

export
empty : Ord k => SortedMap k v
empty = M empty

export
lookup : k -> SortedMap k v -> Maybe v
lookup k = map snd . lookup k . unM

export
insert : k -> v -> SortedMap k v -> SortedMap k v
insert k v = M . insert k v . unM

export
singleton : Ord k => k -> v -> SortedMap k v
singleton = M .: singleton

export
insertFrom : Foldable f => f (k, v) -> SortedMap k v -> SortedMap k v
insertFrom = flip $ foldl $ flip $ uncurry insert

export
delete : k -> SortedMap k v -> SortedMap k v
delete k = M . delete k . unM

export
fromList : Ord k => List (k, v) -> SortedMap k v
fromList = flip insertFrom empty

export
toList : SortedMap k v -> List (k, v)
toList = map unDPair . toList . unM

||| Gets the keys of the map.
export
keys : SortedMap k v -> List k
keys = map fst . toList

||| Gets the values of the map. Could contain duplicates.
export
values : SortedMap k v -> List v
values = map snd . toList

export
implementation Functor (SortedMap k) where
  map f = M . map f . unM

export
implementation Foldable (SortedMap k) where
  foldr f z = foldr f z . values
  foldl f z = foldl f z . values

  null = null . unM

  foldMap f = foldMap f . values

export
implementation Traversable (SortedMap k) where
  traverse f = map M . traverse f . unM

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : (v -> v -> v) -> SortedMap k v -> SortedMap k v -> SortedMap k v
mergeWith f x y = insertFrom inserted x where
  inserted : List (k, v)
  inserted = do
    (k, v) <- toList y
    let v' = (maybe id f $ lookup k x) v
    pure (k, v')

||| Merge two maps using the Semigroup (and by extension, Monoid) operation.
||| Uses mergeWith internally, so the ordering of the left map is kept.
export
merge : Semigroup v => SortedMap k v -> SortedMap k v -> SortedMap k v
merge = mergeWith (<+>)

||| Left-biased merge, also keeps the ordering specified  by the left map.
export
mergeLeft : SortedMap k v -> SortedMap k v -> SortedMap k v
mergeLeft = mergeWith const

||| looks up a key in map, returning the left and right closest values, so that
|||  k1 <= k < k2. If at the end of the beginning and/or end of the sorted map, returns
||| nothing appropriately
export
lookupBetween : key -> SortedMap key val -> (Maybe (key,val), Maybe (key,val))
lookupBetween k = bimap (map unDPair) (map unDPair) . lookupBetween k . unM


||| Returns the leftmost (least) key and value
export
leftMost : SortedMap key val -> Maybe (key,val)
leftMost = map unDPair . leftMost . unM


||| Returns the rightmost (greatest) key and value
export
rightMost : SortedMap key val -> Maybe (key,val)
rightMost = map unDPair . rightMost . unM


export
(Show k, Show v) => Show (SortedMap k v) where
   show m = "fromList " ++ (show $ toList m)

export
(Eq k, Eq v) => Eq (SortedMap k v) where
  (==) = (==) `on` toList

-- TODO: is this the right variant of merge to use for this? I think it is, but
-- I could also see the advantages of using `mergeLeft`. The current approach is
-- strictly more powerful I believe, because `mergeLeft` can be emulated with
-- the `First` monoid. However, this does require more code to do the same
-- thing.
export
Semigroup v => Semigroup (SortedMap k v) where
  (<+>) = merge

||| For `neutral <+> y`, y is rebuilt in `Ord k`, so this is not a "strict" Monoid.
||| However, semantically, it should be equal.
export
(Ord k, Semigroup v) => Monoid (SortedMap k v) where
  neutral = empty

export %inline
Cast (SortedDMap k (const v)) (SortedMap k v) where
  cast = M

export %inline
Cast (SortedMap k v) (SortedDMap k (const v)) where
  cast = unM
