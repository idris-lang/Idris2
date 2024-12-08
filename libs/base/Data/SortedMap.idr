module Data.SortedMap

import Data.SortedMap.Dependent
import Data.Zippable

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

public export %inline
lookup' : SortedMap k v -> k -> Maybe v
lookup' = flip lookup

export
insert : k -> v -> SortedMap k v -> SortedMap k v
insert k v = M . insert k v . unM

||| Inserts a key value pair into a map and merges duplicated values
||| with the given function.
export
insertWith : (v -> v -> v) -> k -> v -> SortedMap k v -> SortedMap k v
insertWith f k v xs =
  case lookup k xs of
    Just x  => insert k (f v x) xs
    Nothing => insert k v xs

public export %inline
insert' : SortedMap k v -> (k, v) -> SortedMap k v
insert' = flip $ uncurry insert

export
singleton : Ord k => k -> v -> SortedMap k v
singleton = M .: singleton

export
insertFrom : Foldable f => f (k, v) -> SortedMap k v -> SortedMap k v
insertFrom = flip $ foldl insert'

public export %inline
insertFrom' : Foldable f => SortedMap k v -> f (k, v) -> SortedMap k v
insertFrom' = flip insertFrom

||| Inserts any foldable of a key value pair into a map and merges duplicated
||| values with the given function.
export
insertFromWith : Foldable f => (v -> v -> v) -> f (k, v) -> SortedMap k v -> SortedMap k v
insertFromWith f = flip $ foldl $ flip $ uncurry $ insertWith f

export
delete : k -> SortedMap k v -> SortedMap k v
delete k = M . delete k . unM

public export %inline
delete' : SortedMap k v -> k -> SortedMap k v
delete' = flip delete

||| Updates or deletes a value based on the decision function
|||
||| The decision function takes information about the presence of the value,
||| and the value itself, if it is present.
||| It returns a new value or the fact that there should be no value as the result.
|||
||| The current implementation performs up to two traversals of the original map
export
update : (Maybe v -> Maybe v) -> k -> SortedMap k v -> SortedMap k v
update f k m = case f $ lookup k m of
  Just v  => insert k v m
  Nothing => delete k m

public export %inline
update' : SortedMap k v -> (Maybe v -> Maybe v) -> k -> SortedMap k v
update' m f x = update f x m

||| Updates existing value, if it is present, and does nothing otherwise
|||
||| The current implementation performs up to two traversals of the original map
export
updateExisting : (v -> v) -> k -> SortedMap k v -> SortedMap k v
updateExisting f k m = case lookup k m of
  Just v  => insert k (f v) m
  Nothing => m

public export %inline
updateExisting' : SortedMap k v -> (v -> v) -> k -> SortedMap k v
updateExisting' m f x = updateExisting f x m

export
fromList : Ord k => List (k, v) -> SortedMap k v
fromList = insertFrom' empty

||| Converts a list of key-value pairs into a map and merges duplicated
||| values with the given function.
export
fromListWith : Ord k => (v -> v -> v) -> List (k, v) -> SortedMap k v
fromListWith f = flip (insertFromWith f) empty

export
toList : SortedMap k v -> List (k, v)
toList = map unDPair . kvList . unM

||| Returns a list of key-value pairs stored in this map
public export %inline
kvList : SortedMap k v -> List (k, v)
kvList = toList

||| Gets the keys of the map.
export
keys : SortedMap k v -> List k
keys = map fst . kvList

||| Gets the values of the map. Could contain duplicates.
export
values : SortedMap k v -> List v
values = map snd . kvList

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

export
implementation Ord k => Zippable (SortedMap k) where
  zipWith f mx my = fromList $ mapMaybe (\(k, x) => (k,) . f x <$> lookup k my) $ kvList mx
  zipWith3 f mx my mz = fromList $ mapMaybe (\(k, x) => (k,) .: f x <$> lookup k my <*> lookup k mz) $ kvList mx
  unzipWith f m = let m' = map f m in (map fst m', map snd m')
  unzipWith3 f m = let m' = map f m in (map fst m', map (fst . snd) m', map (snd . snd) m')

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : (v -> v -> v) -> SortedMap k v -> SortedMap k v -> SortedMap k v
mergeWith f x y = insertFrom inserted x where
  inserted : List (k, v)
  inserted = do
    (k, v) <- kvList y
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


||| Pops the leftmost key and corresponding value from the map
export
pop : SortedMap k v -> Maybe ((k, v), SortedMap k v)
pop = map (bimap unDPair M) . pop . unM

export
(Show k, Show v) => Show (SortedMap k v) where
   show m = "fromList " ++ show (kvList m)

export
(Eq k, Eq v) => Eq (SortedMap k v) where
  (==) = (==) `on` kvList

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
