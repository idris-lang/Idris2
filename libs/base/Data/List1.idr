module Data.List1

import public Data.Zippable
import public Control.Function

%default total

infixr 7 :::

||| Non-empty lists.
public export
record List1 a where
  constructor (:::)
  head : a
  tail : List a

%name List1 xs, ys, zs

------------------------------------------------------------------------
-- Basic functions

public export
fromList : List a -> Maybe (List1 a)
fromList [] = Nothing
fromList (x :: xs) = Just (x ::: xs)

public export
singleton : (x : a) -> List1 a
singleton a = a ::: []

||| Forget that a list is non-empty.
public export
forget : List1 a -> List a
forget (x ::: xs) = x :: xs

export
last : List1 a -> a
last (x ::: xs) = loop x xs where
  loop : a -> List a -> a
  loop x [] = x
  loop _ (x :: xs) = loop x xs

export
init : List1 a -> List a
init (x ::: xs) = loop x xs where
  loop : a -> List a -> List a
  loop x [] = []
  loop x (y :: xs) = x :: loop y xs

export
foldr1By : (func : a -> b -> b) -> (map : a -> b) -> (l : List1 a) -> b
foldr1By f map (x ::: xs) = loop x xs where
  loop : a -> List a -> b
  loop x [] = map x
  loop x (y :: xs) = f x (loop y xs)

public export
foldl1By : (func : b -> a -> b) -> (map : a -> b) -> (l : List1 a) -> b
foldl1By f map (x ::: xs) = foldl f (map x) xs

export
foldr1 : (func : a -> a -> a) -> (l : List1 a) -> a
foldr1 f = foldr1By f id

public export
foldl1 : (func : a -> a -> a) -> (l : List1 a) -> a
foldl1 f = foldl1By f id

public export
length : List1 a -> Nat
length (_ ::: xs) = S (length xs)

------------------------------------------------------------------------
-- Append

public export
appendl : (xs : List1 a) -> (ys : List a) -> List1 a
appendl (x ::: xs) ys = x ::: xs ++ ys

public export
(++) : (xs, ys : List1 a) -> List1 a
(++) xs ys = appendl xs (forget ys)

public export
lappend : (xs : List a) -> (ys : List1 a) -> List1 a
lappend [] ys = ys
lappend (x :: xs) ys = (x ::: xs) ++ ys

------------------------------------------------------------------------
-- Cons/Snoc

public export
cons : (x : a) -> (xs : List1 a) -> List1 a
cons x xs = x ::: forget xs

public export
snoc : (xs : List1 a) -> (x : a) -> List1 a
snoc xs x = xs ++ (singleton x)

public export
unsnoc : (xs : List1 a) -> (List a, a)
unsnoc (x ::: xs) = go x xs where

  go : (x : a) -> (xs : List a) -> (List a, a)
  go x [] = ([], x)
  go x (y :: ys) = let (ini,lst) = go y ys
                   in (x :: ini, lst)

------------------------------------------------------------------------
-- Reverse

public export
reverseOnto : (acc : List1 a) -> (xs : List a) -> List1 a
reverseOnto acc [] = acc
reverseOnto acc (x :: xs) = reverseOnto (x ::: forget acc) xs

public export
reverse : (xs : List1 a) -> List1 a
reverse (x ::: xs) = reverseOnto (singleton x) xs

------------------------------------------------------------------------
-- Instances

public export
Semigroup (List1 a) where
  (<+>) = (++)

public export
Functor List1 where
  map f (x ::: xs) = f x ::: map f xs

public export
Applicative List1 where
  pure x = singleton x
  f ::: fs <*> xs = appendl (map f xs) (fs <*> forget xs)

public export
Monad List1 where
  (x ::: xs) >>= f = appendl (f x) (xs >>= forget . f)

public export
Foldable List1 where
  foldr c n (x ::: xs) = c x (foldr c n xs)
  foldl f z (x ::: xs) = foldl f (f z x) xs
  null _ = False
  toList = forget
  foldMap f (x ::: xs) = f x <+> foldMap f xs

public export
Traversable List1 where
  traverse f (x ::: xs) = [| f x ::: traverse f xs |]

export
Show a => Show (List1 a) where
  show = show . forget

public export
Eq a => Eq (List1 a) where
  (x ::: xs) == (y ::: ys) = x == y && xs == ys

public export
Ord a => Ord (List1 a) where
  compare xs ys = compare (forget xs) (forget ys)

------------------------------------------------------------------------
-- Zippable

public export
Zippable List1 where
  zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith' xs ys
  where
      zipWith' : List a -> List b -> List c
      zipWith' [] _ = []
      zipWith' _ [] = []
      zipWith' (x :: xs) (y :: ys) = f x y :: zipWith' xs ys

  zipWith3 f (x ::: xs) (y ::: ys) (z ::: zs) = f x y z ::: zipWith3' xs ys zs
    where
      zipWith3' : List a -> List b -> List c -> List d
      zipWith3' [] _ _ = []
      zipWith3' _ [] _ = []
      zipWith3' _ _ [] = []
      zipWith3' (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3' xs ys zs

  unzipWith f (x ::: xs) = let (b, c) = f x
                               (bs, cs) = unzipWith' xs in
                               (b ::: bs, c ::: cs)
    where
      unzipWith' : List a -> (List b, List c)
      unzipWith' [] = ([], [])
      unzipWith' (x :: xs) = let (b, c) = f x
                                 (bs, cs) = unzipWith' xs in
                                 (b :: bs, c :: cs)

  unzipWith3 f (x ::: xs) = let (b, c, d) = f x
                                (bs, cs, ds) = unzipWith3' xs in
                                (b ::: bs, c ::: cs, d ::: ds)
    where
      unzipWith3' : List a -> (List b, List c, List d)
      unzipWith3' [] = ([], [], [])
      unzipWith3' (x :: xs) = let (b, c, d) = f x
                                  (bs, cs, ds) = unzipWith3' xs in
                                  (b :: bs, c :: cs, d :: ds)

------------------------------------------------------------------------
-- Uninhabited

export
Uninhabited a => Uninhabited (List1 a) where
  uninhabited (hd ::: _) = uninhabited hd

------------------------------------------------------------------------
-- Filtering

public export %inline
filter : (a -> Bool) -> List1 a -> Maybe $ List1 a
filter f = fromList . filter f . forget
