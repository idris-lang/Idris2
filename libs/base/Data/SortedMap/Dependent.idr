module Data.SortedMap.Dependent

import Data.DPair

import Decidable.Equality

-- TODO: write split

-------------------------------
--- Internal representation ---
-------------------------------

private
data Tree : Nat -> (k : Type) -> (v : k -> Type) -> Ord k -> Type where
  Leaf : (x : k) -> v x -> Tree Z k v o
  Branch2 : Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o
  Branch3 : Tree n k v o -> k -> Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o

branch4 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n k v o -> k -> Tree (S n) k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) k v o -> k -> Tree n k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) k v o -> k -> Tree (S n) k v o -> k -> Tree n k v o -> Tree (S (S n)) k v o
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : Ord k => (x : k) -> Tree n k v o -> Maybe (y : k ** v y) -- may also return an erased `So (x == y)`
treeLookup k (Leaf k' v) =
  if k == k' then
    Just (k' ** v)
  else
    Nothing
treeLookup k (Branch2 t1 k' t2) =
  if k <= k' then
    treeLookup k t1
  else
    treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    treeLookup k t1
  else if k <= k2 then
    treeLookup k t2
  else
    treeLookup k t3

treeInsert' : Ord k => (x : k) -> v x -> Tree n k v o -> Either (Tree n k v o) (Tree n k v o, k, Tree n k v o)
treeInsert' k v (Leaf k' v') =
  case compare k k' of
    LT => Right (Leaf k v, k, Leaf k' v')
    EQ => Left (Leaf k v)
    GT => Right (Leaf k' v', k', Leaf k v)
treeInsert' k v (Branch2 t1 k' t2) =
  if k <= k' then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsert' k v t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k v (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k <= k2 then
      case treeInsert' k v t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsert' k v t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsert : Ord k => (x : k) -> v x -> Tree n k v o -> Either (Tree n k v o) (Tree (S n) k v o)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> (k : Type) -> (v : k -> Type) -> Ord k -> Type
delType Z k v o = ()
delType (S n) k v o = Tree n k v o

treeDelete : Ord k => (n : Nat) -> k -> Tree n k v o -> Either (Tree n k v o) (delType n k v o)
treeDelete _ k (Leaf k' v) =
  if k == k' then
    Right ()
  else
    Left (Leaf k' v)
treeDelete (S Z) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete Z k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete (S Z) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k <= k2 then
    case treeDelete Z k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete Z k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete (S (S n)) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete (S (S n)) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k <= k2 then
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete (S n) k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

treeToList : Tree n k v o -> List (x : k ** v x)
treeToList = treeToList' (:: [])
  where
    -- explicit quantification to avoid conflation with {n} from treeToList
    treeToList' : {0 n : Nat} -> ((x : k ** v x) -> List (x : k ** v x)) -> Tree n k v o -> List (x : k ** v x)
    treeToList' cont (Leaf k v) = cont (k ** v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

----------------------
--- User interface ---
----------------------

export
data SortedDMap : (k : Type) -> (v : k -> Type) -> Type where
  Empty : Ord k => SortedDMap k v
  M : (o : Ord k) => (n : Nat) -> Tree n k v o -> SortedDMap k v

export
empty : Ord k => SortedDMap k v
empty = Empty

export
lookup : (x : k) -> SortedDMap k v -> Maybe (y : k ** v y) -- could return also `So (x == y)`
lookup _ Empty = Nothing
lookup k (M _ t) = treeLookup k t

export
lookupPrecise : DecEq k => (x : k) -> SortedDMap k v -> Maybe (v x)
lookupPrecise x = lookup x >=> \(y ** v) =>
  case decEq x y of
    Yes Refl => Just v
    No _     => Nothing

export
insert : (x : k) -> v x -> SortedDMap k v -> SortedDMap k v
insert k v Empty = M Z (Leaf k v)
insert k v (M _ t) =
  case treeInsert k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
singleton : Ord k => (x : k) -> v x -> SortedDMap k v
singleton k v = insert k v empty

export
insertFrom : Foldable f => f (x : k ** v x) -> SortedDMap k v -> SortedDMap k v
insertFrom = flip $ foldl $ flip $ uncurry insert

export
delete : k -> SortedDMap k v -> SortedDMap k v
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete Z k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S n) t) =
  case treeDelete (S n) k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
fromList : Ord k => List (x : k ** v x) -> SortedDMap k v
fromList = foldl (flip (uncurry insert)) empty

export
toList : SortedDMap k v -> List (x : k ** v x)
toList Empty = []
toList (M _ t) = treeToList t

||| Gets the keys of the map.
export
keys : SortedDMap k v -> List k
keys = map fst . toList

export
values : SortedDMap k v -> List (x : k ** v x)
values = toList

treeMap : ({x : k} -> a x -> b x) -> Tree n k a o -> Tree n k b o
treeMap f (Leaf k v) = Leaf k (f v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3)
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

treeTraverse : Applicative f => ({x : k} -> a x -> f (b x)) -> Tree n k a o -> f (Tree n k b o)
treeTraverse f (Leaf k v) = Leaf k <$> f v
treeTraverse f (Branch2 t1 k t2) =
  Branch2
    <$> treeTraverse f t1
    <*> pure k
    <*> treeTraverse f t2
treeTraverse f (Branch3 t1 k1 t2 k2 t3) =
  Branch3
    <$> treeTraverse f t1
    <*> pure k1
    <*> treeTraverse f t2
    <*> pure k2
    <*> treeTraverse f t3

export
map : ({x : k} -> v x -> w x) -> SortedDMap k v -> SortedDMap k w
map _ Empty = Empty
map f (M _ t) = M _ $ treeMap f t

export
foldl : (acc -> (x : k ** v x) -> acc) -> acc -> SortedDMap k v -> acc
foldl f i = foldl f i . values

export
foldr : ((x : k ** v x) -> acc -> acc) -> acc -> SortedDMap k v -> acc
foldr f i = foldr f i . values

export
foldlM : Monad m => (acc -> (x : k ** v x) -> m acc) -> acc -> SortedDMap k v -> m acc
foldlM f i = foldl (\ma, b => ma >>= flip f b) (pure i)

export
foldMap : Monoid m => (f : (x : k) -> v x -> m) -> SortedDMap k v -> m
foldMap f = foldr ((<+>) . uncurry f) neutral

export
null : SortedDMap k v -> Bool
null Empty   = True
null (M _ _) = False

export
traverse : Applicative f => ({x : k} -> v x -> f (w x)) -> SortedDMap k v -> f (SortedDMap k w)
traverse _ Empty = pure Empty
traverse f (M _ t) = M _ <$> treeTraverse f t

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : DecEq k => ({x : k} -> v x -> v x -> v x) -> SortedDMap k v -> SortedDMap k v -> SortedDMap k v
mergeWith f x y = insertFrom inserted x where
  inserted : List (x : k ** v x)
  inserted = do
    (k ** v) <- toList y
    let v' = (maybe id f $ lookupPrecise k x) v
    pure (k ** v')

||| Merge two maps using the Semigroup (and by extension, Monoid) operation.
||| Uses mergeWith internally, so the ordering of the left map is kept.
export
merge : DecEq k => ({x : k} -> Semigroup (v x)) => SortedDMap k v -> SortedDMap k v -> SortedDMap k v
merge = mergeWith (<+>)

||| Left-biased merge, also keeps the ordering specified  by the left map.
export
mergeLeft : DecEq k => SortedDMap k v -> SortedDMap k v -> SortedDMap k v
mergeLeft = mergeWith const

treeLeftMost : Tree n k v o -> (x : k ** v x)
treeLeftMost (Leaf x y) = (x ** y)
treeLeftMost (Branch2 x _ _) = treeLeftMost x
treeLeftMost (Branch3 x _ _ _ _) = treeLeftMost x

treeRightMost : Tree n k v o -> (x : k ** v x)
treeRightMost (Leaf x y) = (x ** y)
treeRightMost (Branch2 _ _ x) = treeRightMost x
treeRightMost (Branch3 _ _ _ _ x) = treeRightMost x

treeLookupBetween : Ord k => k -> Tree n k v o -> (Maybe (x : k ** v x), Maybe (x : k ** v x))
treeLookupBetween k (Leaf k' v) with (k < k')
  treeLookupBetween k (Leaf k' v) | True = (Nothing, Just (k' ** v))
  treeLookupBetween k (Leaf k' v) | False = (Just (k' ** v), Nothing)
treeLookupBetween k (Branch2 t1 k' t2) with (k < k')
  treeLookupBetween k (Branch2 t1 k' t2) | True = -- k < k'
    let (lower, upper) = treeLookupBetween k t1 in
    (lower, upper <|> pure (treeLeftMost t2))
  treeLookupBetween k (Branch2 t1 k' t2) | False = -- k >= k'
    let (lower, upper) = treeLookupBetween k t2 in
    (lower <|> pure (treeRightMost t1), upper)
treeLookupBetween k (Branch3 t1 k1 t2 k2 t3) with (k < k1)
  treeLookupBetween k (Branch3 t1 k1 t2 k2 t3) | True = treeLookupBetween k (Branch2 t1 k1 t2)
  treeLookupBetween k (Branch3 t1 k1 t2 k2 t3) | False with (k < k2)
    treeLookupBetween k (Branch3 t1 k1 t2 k2 t3) | False | False = treeLookupBetween k (Branch2 t2 k2 t3)
    treeLookupBetween k (Branch3 t1 k1 t2 k2 t3) | False | True = --k1 <= k < k2
      let (lower, upper) = treeLookupBetween k (Branch2 t1 k1 t2) in
      (lower, upper <|> pure (treeLeftMost t3))

||| looks up a key in map, returning the left and right closest values, so that
|||  k1 <= k < k2. If at the end of the beginning and/or end of the sorted map, returns
||| nothing appropriately
export
lookupBetween : k -> SortedDMap k v -> (Maybe (x : k ** v x), Maybe (x : k ** v x))
lookupBetween k Empty = (Nothing, Nothing)
lookupBetween k (M _ t) = treeLookupBetween k t


||| Returns the leftmost (least) key and value
export
leftMost : SortedDMap k v -> Maybe (x : k ** v x)
leftMost Empty = Nothing
leftMost (M _ t) = Just $ treeLeftMost t


||| Returns the rightmost (greatest) key and value
export
rightMost : SortedDMap k v -> Maybe (x : k ** v x)
rightMost Empty = Nothing
rightMost (M _ t) = Just $ treeRightMost t

export
(Show k, {x : k} -> Show (v x)) => Show (SortedDMap k v) where
   show m = "fromList " ++ (show $ toList m)

export
(DecEq k, {x : k} -> Eq (v x)) => Eq (SortedDMap k v) where
  (==) = (==) `on` toList

export
strictSubmap : DecEq k => ({x : k} -> Eq (v x)) => (sub : SortedDMap k v) -> (sup : SortedDMap k v) -> Bool
strictSubmap sub sup = all (\(k ** v) => Just v == lookupPrecise k sup) $ toList sub

-- TODO: is this the right variant of merge to use for this? I think it is, but
-- I could also see the advantages of using `mergeLeft`. The current approach is
-- strictly more powerful I believe, because `mergeLeft` can be emulated with
-- the `First` monoid. However, this does require more code to do the same
-- thing.
export
DecEq k => ({x : k} -> Semigroup (v x)) => Semigroup (SortedDMap k v) where
  (<+>) = merge

||| For `neutral <+> y`, y is rebuilt in `Ord k`, so this is not a "strict" Monoid.
||| However, semantically, it should be equal.
export
DecEq k => Ord k => ({x : k} -> Semigroup (v x)) => Monoid (SortedDMap k v) where
  neutral = empty
