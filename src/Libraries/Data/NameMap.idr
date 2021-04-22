module Libraries.Data.NameMap

import Core.Name

-- Hand specialised map, for efficiency...

%default total

Key : Type
Key = Name

-- TODO: write split

private
data Tree : Nat -> Type -> Type where
  Leaf : Key -> v -> Tree Z v
  Branch2 : Tree n v -> Key -> Tree n v -> Tree (S n) v
  Branch3 : Tree n v -> Key -> Tree n v -> Key -> Tree n v -> Tree (S n) v

Show v => Show (Tree n v) where
  show (Leaf k v) = "Leaf: " ++ show k ++ " -> " ++ show v ++ "\n"
  show (Branch2 t1 k t2) = "Branch2: " ++ show t1 ++ "\n < " ++ show k ++ "\n" ++ show t2 ++ "\n"
  show (Branch3 t1 k1 t2 k2 t3) = "Branch3: " ++ show t1 ++ "\n < " ++ show k1 ++ "\n" ++ show t2 ++ "\n < " ++ show k2 ++ "\n" ++ show t3 ++ "\n"

branch4 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v -> Key ->
  Tree n v ->
  Tree (S (S n)) v
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n v -> Key -> Tree (S n) v -> Key -> Tree (S n) v -> Tree (S (S n)) v
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) v -> Key -> Tree n v -> Key -> Tree (S n) v -> Tree (S (S n)) v
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) v -> Key -> Tree (S n) v -> Key -> Tree n v -> Tree (S (S n)) v
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : Key -> Tree n v -> Maybe v
treeLookup k (Leaf k' v) =
  if k == k' then
    Just v
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

treeInsert' : Key -> v -> Tree n v -> Either (Tree n v) (Tree n v, Key, Tree n v)
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

treeInsert : Key -> v -> Tree n v -> Either (Tree n v) (Tree (S n) v)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> Type -> Type
delType Z v = ()
delType (S n) v = Tree n v

treeDelete : {n : _} ->
             Key -> Tree n v -> Either (Tree n v) (delType n v)
treeDelete k (Leaf k' v) =
  if k == k' then
    Right ()
  else
    Left (Leaf k' v)
treeDelete {n=S Z} k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete {n=S Z} k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k <= k2 then
    case treeDelete k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete {n=S (S _)} k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete {n=(S (S _))} k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k <= k2 then
    case treeDelete k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

treeToList : Tree n v -> List (Key, v)
treeToList = treeToList' []
  where
    treeToList' : forall n . List (Key, v) -> Tree n v -> List (Key, v)
    treeToList' rest (Leaf k v) = (k, v) :: rest
    treeToList' rest (Branch2 t1 _ t2)
        = treeToList' (treeToList' rest t2) t1
    treeToList' rest (Branch3 t1 _ t2 _ t3)
        = treeToList' (treeToList' (treeToList' rest t3) t2) t1

export
data NameMap : Type -> Type where
  Empty : NameMap v
  M : (n : Nat) -> Tree n v -> NameMap v

export
Show v => Show (NameMap v) where
  show Empty = "Empty NameMap"
  show (M n t) = "NameMap M(" ++ show n ++ "):\n" ++ show t

export
empty : NameMap v
empty = Empty

export
singleton : Name -> v -> NameMap v
singleton n v = M Z $ Leaf n v

export
lookup : Name -> NameMap v -> Maybe v
lookup _ Empty = Nothing
lookup k (M _ t) = treeLookup k t

export
insert : Name -> v -> NameMap v -> NameMap v
insert k v Empty = M Z (Leaf k v)
insert k v (M _ t) =
  case treeInsert k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
insertFrom : List (Name, v) -> NameMap v -> NameMap v
insertFrom = flip $ foldl $ flip $ uncurry insert

export
delete : Name -> NameMap v -> NameMap v
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S _) t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
fromList : List (Name, v) -> NameMap v
fromList l = foldl (flip (uncurry insert)) empty l

export
toList : NameMap v -> List (Name, v)
toList Empty = []
toList (M _ t) = treeToList t

||| Gets the Keys of the map.
export
keys : NameMap v -> List Name
keys = map fst . toList

||| Gets the values of the map. Could contain duplicates.
export
values : NameMap v -> List v
values = map snd . toList

treeMap : (a -> b) -> Tree n a -> Tree n b
treeMap f (Leaf k v) = Leaf k (f v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3)
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

export
implementation Functor NameMap where
  map _ Empty = Empty
  map f (M n t) = M _ (treeMap f t)

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : (v -> v -> v) -> NameMap v -> NameMap v -> NameMap v
mergeWith f x y = insertFrom inserted x where
  inserted : List (Key, v)
  inserted = do
    (k, v) <- toList y
    let v' = (maybe id f $ lookup k x) v
    pure (k, v')

||| Merge two maps using the Semigroup (and by extension, Monoid) operation.
||| Uses mergeWith internally, so the ordering of the left map is kept.
export
merge : Semigroup v => NameMap v -> NameMap v -> NameMap v
merge = mergeWith (<+>)

||| Left-biased merge, also keeps the ordering specified  by the left map.
export
mergeLeft : NameMap v -> NameMap v -> NameMap v
mergeLeft = mergeWith const

-- TODO: is this the right variant of merge to use for this? I think it is, but
-- I could also see the advantages of using `mergeLeft`. The current approach is
-- strictly more powerful I believe, because `mergeLeft` can be emulated with
-- the `First` monoid. However, this does require more code to do the same
-- thing.
export
Semigroup v => Semigroup (NameMap v) where
  (<+>) = merge

export
(Semigroup v) => Monoid (NameMap v) where
  neutral = empty


treeFilterByM : Monad m => (Key -> m Bool) -> Tree n v -> m (NameMap v)
treeFilterByM test = loop empty where

  loop : NameMap v -> Tree _ v -> m (NameMap v)
  loop acc (Leaf k v)
    = do True <- test k | _ => pure acc
         pure (insert k v acc)
  loop acc (Branch2 t1 _ t2)
    = do acc <- loop acc t1
         loop acc t2
  loop acc (Branch3 t1 _ t2 _ t3)
    = do acc <- loop acc t1
         acc <- loop acc t2
         loop acc t3

export
filterByM : Monad m => (Name -> m Bool) -> NameMap v -> m (NameMap v)
filterByM test Empty = pure Empty
filterByM test (M _ t) = treeFilterByM test t

treeMapMaybeM : Monad m => (Key -> m (Maybe a)) -> Tree _ v -> m (NameMap a)
treeMapMaybeM test = loop empty where

  loop : NameMap a -> Tree _ v -> m (NameMap a)
  loop acc (Leaf k v)
    = do Just a <- test k | _ => pure acc
         pure (insert k a acc)
  loop acc (Branch2 t1 _ t2)
    = do acc <- loop acc t1
         loop acc t2
  loop acc (Branch3 t1 _ t2 _ t3)
    = do acc <- loop acc t1
         acc <- loop acc t2
         loop acc t3

export
mapMaybeM : Monad m => (Name -> m (Maybe a)) -> NameMap v -> m (NameMap a)
mapMaybeM test Empty = pure Empty
mapMaybeM test (M _ t) = treeMapMaybeM test t
