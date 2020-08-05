module Data.List1

%default total

public export
record List1 a where
  constructor (::)
  head : a
  tail : List a

export
last : List1 a -> a
last (x :: xs) = go x xs where

  go : a -> List a -> a
  go x [] = x
  go _ (y :: ys) = go y ys

public export
toList : (1 xs : List1 a) -> List a
toList (x :: xs) = x :: xs

export
cons : (1 x : a) -> (1 xs : List1 a) -> List1 a
cons x xs = x :: toList xs

public export
reverseOnto : (1 acc : List1 a) -> (1 xs : List a) -> List1 a
reverseOnto acc []        = acc
reverseOnto acc (x :: xs) = reverseOnto (x :: toList acc) xs

public export
reverse : (1 xs : List1 a) -> List1 a
reverse (x :: xs) = reverseOnto [x] xs

export
fromList : (1 xs : List a) -> Maybe (List1 a)
fromList [] = Nothing
fromList (x :: xs) = Just (x :: xs)

export
appendl : (1 xs : List1 a) -> (1 ys : List a) -> List1 a
appendl (x :: xs) ys = x :: xs ++ ys

export
append : (1 xs, ys : List1 a) -> List1 a
append xs ys = appendl xs (toList ys)

export
lappend : (1 xs : List a) -> (1 ys : List1 a) -> List1 a
lappend [] ys = ys
lappend (x :: xs) ys = append (x :: xs) ys

export
Functor List1 where
  map f (x :: xs) = f x :: map f xs

export
Foldable List1 where
  foldr c n (x :: xs) = c x (foldr c n xs)

export
Show a => Show (List1 a) where
  show = show . toList

export
Applicative List1 where
  pure x = [x]
  f :: fs <*> xs = appendl (map f xs) (fs <*> toList xs)

export
Monad List1 where
  (x :: xs) >>= f = appendl (f x) (xs >>= toList . f)
