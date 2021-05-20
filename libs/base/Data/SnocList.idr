||| A Reversed List
module Data.SnocList

import Decidable.Equality
import Data.List

%default total

infixl 7 <><
infixr 6 <>>

||| 'fish': Action of lists on snoc-lists
public export
(<><) : SnocList a -> List a -> SnocList a
sx <>< [] = sx
sx <>< (x :: xs) = sx :< x <>< xs

||| 'chips': Action of snoc-lists on lists
public export
(<>>) : SnocList a -> List a -> List a
Lin       <>> xs = xs
(sx :< x) <>> xs = sx <>> x :: xs

Cast (SnocList a) (List a) where
  cast sx = sx <>> []

Cast (List a) (SnocList a) where
  cast xs = Lin <>< xs

||| Transform to a list but keeping the contents in the spine order (term depth).
public export
asList : SnocList type -> List type
asList = (reverse . cast)


public export
Eq a => Eq (SnocList a) where
  (==) Lin Lin = True
  (==) (sx :< x) (sy :< y) = x == y && sx == sy
  (==) _ _ = False


public export
Ord a => Ord (SnocList a) where
  compare Lin Lin = EQ
  compare Lin (sx :< x) = LT
  compare (sx :< x) Lin = GT
  compare (sx :< x) (sy :< y)
    = case compare sx sy of
        EQ => compare x y
        c  => c

||| True iff input is Lin
public export
isLin : SnocList a -> Bool
isLin Lin = True
isLin (sx :< x) = False

||| True iff input is (:<)
public export
isSnoc : SnocList a -> Bool
isSnoc Lin     = False
isSnoc (sx :< x) = True

public export
(++) : (sx, sy : SnocList a) -> SnocList a
(++) sx Lin = sx
(++) sx (sy :< y) = (sx ++ sy) :< y

public export
length : SnocList a -> Nat
length Lin = Z
length (sx :< x) = length sx + 1

export
Show a => Show (SnocList a) where
  show xs = "[< " ++ show' "" xs ++ "]"
    where
      show' : String -> SnocList a -> String
      show' acc Lin       = acc
      show' acc (Lin :< x)= show x ++ acc
      show' acc (xs :< x) = show' (", " ++ show x ++ acc) xs


public export
Functor SnocList where
  map f Lin = Lin
  map f (sx :< x) = (map f sx) :< (f x)


public export
Semigroup (SnocList a) where
  (<+>) = (++)

public export
Monoid (SnocList a) where
  neutral = Lin


||| Check if something is a member of a list using the default Boolean equality.
public export
elem : Eq a => a -> SnocList a -> Bool
elem x Lin = False
elem x (sx :< y) = x == y || elem x sx
