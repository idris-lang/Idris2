module Libraries.Data.NameSet

import Core.Name

-- Hand specialised set, for efficiency...
-- Unlike SortedSet:
-- 1. we don't store values of type () in the leaves
-- 2. we don't have the (Ord a =>) indirection

%default total

Key : Type
Key = Name

-- TODO: write split

private
data Tree : Nat -> Type where
  Leaf : Key -> Tree Z
  Branch2 : Tree n -> Key -> Tree n -> Tree (S n)
  Branch3 : Tree n -> Key -> Tree n -> Key -> Tree n -> Tree (S n)

Show (Tree n) where
  show (Leaf k) = "Leaf: " ++ show k ++ "\n"
  show (Branch2 t1 k t2) = "Branch2: " ++ show t1 ++ "\n < " ++ show k ++ "\n" ++ show t2 ++ "\n"
  show (Branch3 t1 k1 t2 k2 t3) = "Branch3: " ++ show t1 ++ "\n < " ++ show k1 ++ "\n" ++ show t2 ++ "\n < " ++ show k2 ++ "\n" ++ show t3 ++ "\n"

branch4 :
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n ->
  Tree (S (S n))
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n ->
  Tree (S (S n))
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n ->
  Tree (S (S n))
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n -> Key ->
  Tree n ->
  Tree (S (S n))
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n -> Key -> Tree (S n) -> Key -> Tree (S n) -> Tree (S (S n))
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) -> Key -> Tree n -> Key -> Tree (S n) -> Tree (S (S n))
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) -> Key -> Tree (S n) -> Key -> Tree n -> Tree (S (S n))
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : Key -> Tree n -> Bool
treeLookup k (Leaf k') = k == k'
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

treeInsert' : Key -> Tree n -> Either (Tree n) (Tree n, Key, Tree n)
treeInsert' k (Leaf k') =
  case compare k k' of
    LT => Right (Leaf k, k, Leaf k')
    EQ => Left (Leaf k)
    GT => Right (Leaf k', k', Leaf k)
treeInsert' k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeInsert' k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsert' k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeInsert' k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k <= k2 then
      case treeInsert' k t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsert' k t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsert : Key -> Tree n -> Either (Tree n) (Tree (S n))
treeInsert k t =
  case treeInsert' k t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> Type
delType Z = ()
delType (S n) = Tree n

treeDelete : {n : _} ->
             Key -> Tree n -> Either (Tree n) (delType n)
treeDelete k (Leaf k') =
  if k == k' then
    Right ()
  else
    Left (Leaf k')
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

treeToList : Tree n -> List Key
treeToList = treeToList' []
  where
    treeToList' : forall n . List Key -> Tree n -> List Key
    treeToList' rest (Leaf k) = k :: rest
    treeToList' rest (Branch2 t1 _ t2)
        = treeToList' (treeToList' rest t2) t1
    treeToList' rest (Branch3 t1 _ t2 _ t3)
        = treeToList' (treeToList' (treeToList' rest t3) t2) t1

export
data NameSet : Type where
  Empty : NameSet
  M : (n : Nat) -> Tree n -> NameSet

export
Show NameSet where
  show Empty = "Empty NameMap"
  show (M n t) = "NameMap M(" ++ show n ++ "):\n" ++ show t

export
empty : NameSet
empty = Empty

export
singleton : Name -> NameSet
singleton n = M Z $ Leaf n

export
null : NameSet -> Bool
null Empty = True
null _ = False

export
elem : Name -> NameSet -> Bool
elem _ Empty = False
elem k (M _ t) = treeLookup k t

export
insert : Name -> NameSet -> NameSet
insert k Empty = M Z (Leaf k)
insert k (M _ t) =
  case treeInsert k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
insertFrom : List Name -> NameSet -> NameSet
insertFrom = flip $ foldl $ flip insert

export
delete : Name -> NameSet -> NameSet
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
fromList : List Name -> NameSet
fromList l = insertFrom l empty

export
toList : NameSet -> List Name
toList Empty = []
toList (M _ t) = treeToList t

export
union : NameSet -> NameSet -> NameSet
union x y = insertFrom (toList x) y

export
Semigroup NameSet where
  (<+>) = union

export
Monoid NameSet where
  neutral = empty


treeFilterBy : (Key -> Bool) -> Tree n -> NameSet
treeFilterBy test = loop empty where

  loop : NameSet -> Tree _ -> NameSet
  loop acc (Leaf k)
    = let True = test k | _ => acc in
      insert k acc
  loop acc (Branch2 t1 _ t2)
    = loop (loop acc t1) t2
  loop acc (Branch3 t1 _ t2 _ t3)
    = loop (loop (loop acc t1) t2) t3

treeFilterByM : Monad m => (Key -> m Bool) -> Tree n -> m NameSet
treeFilterByM test = loop empty where

  loop : NameSet -> Tree _ -> m NameSet
  loop acc (Leaf k)
    = do True <- test k | _ => pure acc
         pure (insert k acc)
  loop acc (Branch2 t1 _ t2)
    = do acc <- loop acc t1
         loop acc t2
  loop acc (Branch3 t1 _ t2 _ t3)
    = do acc <- loop acc t1
         acc <- loop acc t2
         loop acc t3

export
filterBy : (Name -> Bool) -> NameSet -> NameSet
filterBy test Empty = Empty
filterBy test (M _ t) = treeFilterBy test t

export
filterByM : Monad m => (Name -> m Bool) -> NameSet -> m NameSet
filterByM test Empty = pure Empty
filterByM test (M _ t) = treeFilterByM test t

treeFoldl : (acc -> Name -> acc) -> acc -> Tree _ -> acc
treeFoldl f z (Leaf k) = f z k
treeFoldl f z (Branch2 l _ r) = treeFoldl f (treeFoldl f z l) r
treeFoldl f z (Branch3 l _ m _ r) = treeFoldl f (treeFoldl f (treeFoldl f z l) m) r

export
foldlNames : (acc -> Name -> acc) -> acc -> NameSet -> acc
foldlNames f z Empty = z
foldlNames f z (M _ t) = treeFoldl f z t
