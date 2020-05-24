module Data.List.NonEmpty

%default total

public export
record List1 (a : Type) where
  constructor (::)
  head : a
  tail : List a

export
last : List1 a -> a
last (x :: xs) = foldl (flip const) x xs

||| Implementations

public export
Functor List1 where

  map f (x :: xs) = f x :: map f xs

public export
Foldable List1 where

  foldr c n (x :: xs) = c x (foldr c n xs)
  foldl c n (x :: xs) = foldl c (c n x) xs

||| We define a specialised version of `toList` because the one defined using
||| a `Foldable` constraint would have to needlessly go through the whole tail.
export
toList : List1 a -> List a
toList (x :: xs) = x :: xs

export
cons : a -> List1 a -> List1 a
cons x (y :: ys) = x :: (y :: ys)

export
reverseOnto : List1 a -> List a -> List1 a
reverseOnto = foldl (flip cons)

export
reverse : List1 a -> List1 a
reverse (x :: xs) = reverseOnto (x :: []) xs
