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
  Leaf2 : Key -> Key -> Tree Z
  Branch2 : Tree n -> Key -> Tree n -> Tree (S n)
  Branch3 : Tree n -> Key -> Tree n -> Key -> Tree n -> Tree (S n)

Show (Tree n) where
  show (Leaf k) = "Leaf: " ++ show k ++ "\n"
  show (Leaf2 k1 k2) = "Leaf2: " ++ show k1 ++ ", " ++ show k2 ++ "\n"
  show (Branch2 t1 k t2) = "Branch2: " ++ show t1 ++ "\n < " ++ show k ++ "\n" ++ show t2 ++ "\n"
  show (Branch3 t1 k1 t2 k2 t3) = "Branch3: " ++ show t1 ++ "\n < " ++ show k1 ++ "\n" ++ show t2 ++ "\n < " ++ show k2 ++ "\n" ++ show t3 ++ "\n"

treeLookup : Key -> Tree n -> Bool
treeLookup k (Leaf k') = k == k'
treeLookup k (Leaf2 k1 k2) = case compare k k1 of
  LT => False
  EQ => True
  GT => k == k2
treeLookup k (Branch2 t1 k' t2) = case compare k k' of
  LT => treeLookup k t1
  EQ => True
  GT => treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) = case compare k k1 of
  LT => treeLookup k t1
  EQ => True
  GT => case compare k k2 of
    LT => treeLookup k t2
    EQ => True
    GT => treeLookup k t3

treeInsert' : Key -> Tree n -> Either (Tree n) (Tree n, Key, Tree n)
treeInsert' k t@(Leaf k') = case compare k k' of
    LT => Left (Leaf2 k k')
    EQ => Left t
    GT => Left (Leaf2 k' k)
treeInsert' k t@(Leaf2 k1 k2) = case compare k k1 of
  LT => Right (Leaf k, k1, Leaf k2)
  EQ => Left t
  GT => case compare k k2 of
    LT => Right (Leaf k1, k, Leaf k2)
    EQ => Left t
    GT => Right (Leaf k1, k2, Leaf k)
treeInsert' k t@(Branch2 t1 k' t2) = case compare k k' of
  LT => case treeInsert' k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  EQ => Left t
  GT => case treeInsert' k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k t@(Branch3 t1 k1 t2 k2 t3) = case compare k k1 of
  LT => case treeInsert' k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  EQ => Left t
  GT => case compare k k2 of
    LT => case treeInsert' k t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    EQ => Left t
    GT => case treeInsert' k t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsert : Key -> Tree n -> Either (Tree n) (Tree (S n))
treeInsert k t =
  case treeInsert' k t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

treeToList : Tree n -> List Key
treeToList t = treeToList' t []
  where
    treeToList' : Tree _ -> List Key -> List Key
    treeToList' (Leaf k) = (k ::)
    treeToList' (Leaf2 k1 k2) = ([k1,k2] ++)
    treeToList' (Branch2 t1 k t2)
        = treeToList' t1
        . (k ::)
        . treeToList' t2
    treeToList' (Branch3 t1 k1 t2 k2 t3)
        = treeToList' t1
        . (k1 ::)
        . treeToList' t2
        . (k2 ::)
        . treeToList' t3

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
treeFilterBy test t = loop t empty where

  loop : Tree _ -> NameSet -> NameSet
  loop (Leaf k)
    = ifThenElse (test k) (insert k) id
  loop (Leaf2 k1 k2)
    = ifThenElse (test k1) (insert k1) id
    . ifThenElse (test k2) (insert k2) id
  loop (Branch2 t1 k t2)
    = loop t2
    . ifThenElse (test k) (insert k) id
    . loop t1
  loop (Branch3 t1 k1 t2 k2 t3)
    = loop t3
    . ifThenElse (test k2) (insert k2) id
    . loop t2
    . ifThenElse (test k1) (insert k1) id
    . loop t1

treeFilterByM : Monad m => (Key -> m Bool) -> Tree n -> m NameSet
treeFilterByM test = loop empty where

  loop : NameSet -> Tree _ -> m NameSet
  loop acc (Leaf k)
    = pure
    $ ifThenElse !(test k) (insert k) id
    $ acc
  loop acc (Leaf2 k1 k2)
    = pure
    $ ifThenElse !(test k1) (insert k1) id
    $ ifThenElse !(test k2) (insert k2) id
    $ acc
  loop acc (Branch2 t1 k t2)
    = do acc <- loop acc t1
         let acc = ifThenElse !(test k) (insert k) id acc
         loop acc t2
  loop acc (Branch3 t1 k1 t2 k2 t3)
    = do acc <- loop acc t1
         let acc = ifThenElse !(test k1) (insert k1) id acc
         acc <- loop acc t2
         let acc = ifThenElse !(test k2) (insert k2) id acc
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
treeFoldl f z (Leaf2 k1 k2) = f (f z k1) k2
treeFoldl f z (Branch2 l k r) = treeFoldl f (f (treeFoldl f z l) k) r
treeFoldl f z (Branch3 l k1 m k2 r)
  = treeFoldl f (f (treeFoldl f (f (treeFoldl f z l) k1) m) k2) r

export
foldlNames : (acc -> Name -> acc) -> acc -> NameSet -> acc
foldlNames f z Empty = z
foldlNames f z (M _ t) = treeFoldl f z t

treeSize : Tree _ -> Nat -> Nat
treeSize (Leaf n) = S
treeSize (Leaf2 _ _) = (2+)
treeSize (Branch2 t1 _ t2) = treeSize t1 . treeSize t2 . (1+)
treeSize (Branch3 t1 _ t2 _ t3) = treeSize t1 . treeSize t2 . treeSize t3 . (2+)

export
size : NameSet -> Nat
size Empty = 0
size (M _ t) = treeSize t 0
