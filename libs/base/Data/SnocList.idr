||| A Reversed List
module Data.SnocList

import Decidable.Equality
import Data.List

%default total

||| 'fish': Action of lists on snoc-lists
public export
(<><) : SnocList a -> List a -> SnocList a
sx <>< [] = sx
sx <>< (x :: xs) = sx :< x <>< xs

||| 'chips': Action of snoc-lists on lists
public export
(<>>) : SnocList a -> List a -> List a
Empty     <>> xs = xs
(sx :< x) <>> xs = sx <>> x :: xs

||| Reverse the snoc-list and make a list.
public export
toList : SnocList type -> List type
toList Empty = Nil
toList (sx :< x) = x :: toList sx

||| Transform to a list but keeping the contents in the 'correct' order (term depth).
public export
asList : SnocList type -> List type
asList = (reverse . toList)


public export
Eq a => Eq (SnocList a) where
  (==) Empty Empty = True
  (==) (sx :< x) (sy :< y) = x == y && sx == sy
  (==) _ _ = False


public export
Ord a => Ord (SnocList a) where
  compare Empty Empty = EQ
  compare Empty (sx :< x) = LT
  compare (sx :< x) Empty = GT
  compare (sx :< x) (sy :< y)
    = case compare sx sy of
        EQ => compare x y
        c  => c

||| True iff input is Empty
public export
isEmpty : SnocList a -> Bool
isEmpty Empty = True
isEmpty (sx :< x) = False

||| True iff input is (:<)
public export
isSnoc : SnocList a -> Bool
isSnoc Empty     = False
isSnoc (sx :< x) = True

public export
(++) : (sx, sy : SnocList a) -> SnocList a
(++) sx Empty = sx
(++) sx (sy :< y) = (sx ++ sy) :< y

public export
length : SnocList a -> Nat
length Empty = Z
length (sx :< x) = length sx + 1

export
Show a => Show (SnocList a) where
  show xs = "[< " ++ show' "" xs ++ "]"
    where
      show' : String -> SnocList a -> String
      show' acc Empty     = acc
      show' acc [< x]     = show x ++ acc
      show' acc (xs :< x) = show' (", " ++ show x ++ acc) xs


public export
Functor SnocList where
  map f Empty = Empty
  map f (sx :< x) = (map f sx) :< (f x)


public export
Semigroup (SnocList a) where
  (<+>) = (++)

public export
Monoid (SnocList a) where
  neutral = Empty


||| Check if something is a member of a list using the default Boolean equality.
public export
elem : Eq a => a -> SnocList a -> Bool
elem x Empty = False
elem x (sx :< y) = x == y || elem x sx
