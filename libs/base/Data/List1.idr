module Data.List1

%default total

infixr 7 :::

public export
record List1 a where
  constructor (:::)
  head : a
  tail : List a

------------------------------------------------------------------------
-- Conversion

||| Forget that a list is non-empty
public export
forget : (xs : List1 a) -> List a
forget (x ::: xs) = x :: xs

||| Check whether a list is non-empty
export
fromList : (xs : List a) -> Maybe (List1 a)
fromList [] = Nothing
fromList (x :: xs) = Just (x ::: xs)

------------------------------------------------------------------------
-- Basic functions

public export
singleton : (x : a) -> List1 a
singleton a = a ::: []

export
last : List1 a -> a
last (x ::: xs) = loop x xs where

  loop : a -> List a -> a
  loop x [] = x
  loop _ (x :: xs) = loop x xs

export
foldr1' : (a -> b -> b) -> (a -> b) -> List1 a -> b
foldr1' c n (x ::: xs) = loop x xs where

  loop : a -> List a -> b
  loop a [] = n a
  loop a (x :: xs) = c a (loop x xs)

export
foldr1 : (a -> a -> a) -> List1 a -> a
foldr1 c = foldr1' c id

export
foldl1 : (a -> b) -> (b -> a -> b) -> List1 a -> b
foldl1 n c (x ::: xs) = foldl c (n x) xs

------------------------------------------------------------------------
-- Append

export
appendl : (xs : List1 a) -> (ys : List a) -> List1 a
appendl (x ::: xs) ys = x ::: xs ++ ys

export
append : (xs, ys : List1 a) -> List1 a
append xs ys = appendl xs (forget ys)

export
lappend : (xs : List a) -> (ys : List1 a) -> List1 a
lappend [] ys = ys
lappend (x :: xs) ys = append (x ::: xs) ys

------------------------------------------------------------------------
-- Cons/Snoc

public export
cons : (x : a) -> (xs : List1 a) -> List1 a
cons x xs = x ::: forget xs

export
snoc : (xs : List1 a) -> (x : a) -> List1 a
snoc xs x = append xs (singleton x)

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

export
Semigroup (List1 a) where
  (<+>) = append

export
Functor List1 where
  map f (x ::: xs) = f x ::: map f xs

export
Applicative List1 where
  pure x = singleton x
  f ::: fs <*> xs = appendl (map f xs) (fs <*> forget xs)

export
Monad List1 where
  (x ::: xs) >>= f = appendl (f x) (xs >>= forget . f)

export
Foldable List1 where
  foldr c n (x ::: xs) = c x (foldr c n xs)
  null _ = False

export
Traversable List1 where
  traverse f (x ::: xs) = [| f x ::: traverse f xs |]

export
Show a => Show (List1 a) where
  show = show . forget

export
Eq a => Eq (List1 a) where
  (x ::: xs) == (y ::: ys) = x == y && xs == ys

export
Ord a => Ord (List1 a) where
  compare xs ys = compare (forget xs) (forget ys)

------------------------------------------------------------------------
-- Properties

export
consInjective : the (List1 a) (x ::: xs) === (y ::: ys) -> (x === y, xs === ys)
consInjective Refl = (Refl, Refl)
