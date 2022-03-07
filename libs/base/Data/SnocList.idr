||| A Reversed List
module Data.SnocList

import Data.List
import Data.Fin

%default total

export
Cast (SnocList a) (List a) where
  cast sx = sx <>> []

export
Cast (List a) (SnocList a) where
  cast xs = Lin <>< xs

%transform "fastConcat" concat {t = SnocList} {a = String} = fastConcat . cast

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
length (sx :< x) = S $ length sx

export
Show a => Show (SnocList a) where
  show xs = concat ("[< " :: intersperse ", " (show' [] xs) ++ ["]"])
    where
      show' : List String -> SnocList a -> List String
      show' acc Lin       = acc
      show' acc (xs :< x) = show' (show x :: acc) xs

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

public export
Foldable SnocList where
  foldr f z = foldr f z . (<>> [])

  foldl f z Lin = z
  foldl f z (xs :< x) = f (foldl f z xs) x

  null Lin      = True
  null (_ :< _) = False

  toList = (<>> [])

  foldMap f = foldl (\xs, x => xs <+> f x) neutral

public export
Applicative SnocList where
  pure = (:<) Lin
  fs <*> xs = concatMap (flip map xs) fs

public export
Monad SnocList where
  xs >>= k = concatMap k xs

public export
Traversable SnocList where
  traverse _ Lin = pure Lin
  traverse f (xs :< x) = [| traverse f xs :< f x |]

public export
Alternative SnocList where
  empty = Lin
  xs <|> ys = xs ++ ys

||| Find the first element of the snoc-list that satisfies the predicate.
public export
find : (a -> Bool) -> SnocList a -> Maybe a
find p Lin = Nothing
find p (xs :< x) = if p x then Just x else find p xs

||| Satisfiable if `k` is a valid index into `xs`.
|||
||| @ k  the potential index
||| @ xs the snoc-list into which k may be an index
public export
data InBounds : (k : Nat) -> (xs : SnocList a) -> Type where
    ||| Z is a valid index into any cons cell
    InFirst : InBounds Z (xs :< x)
    ||| Valid indices can be extended
    InLater : InBounds k xs -> InBounds (S k) (xs :< x)

||| Find the index and proof of InBounds of the first element (if exists) of a
||| snoc-list that satisfies the given test, else `Nothing`.
public export
findIndex : (a -> Bool) -> (xs : SnocList a) -> Maybe $ Fin (length xs)
findIndex _ Lin = Nothing
findIndex p (xs :< x) = if p x
  then Just FZ
  else FS <$> findIndex p xs
