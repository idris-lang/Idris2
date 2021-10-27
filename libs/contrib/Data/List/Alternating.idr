module Data.List.Alternating

import Data.Bifoldable
import Data.List

infixl 5 +>
infixr 5 <+

mutual
    namespace Fence
        ||| Non-empty list, starting and ending with an a, where adjacent elements alternate
        ||| between types a and b.
        ||| We can think of this type as:
        ||| - A fence, with the `a`s as fence-posts, and the `b`s as panels.
        ||| - A non-empty list of `a`s, separated by `b`s
        ||| - A list of `b`s, separated by, and surrounded by, `a`s
        public export
        data Fence a b = (::) a (PairList b a)

    namespace PairList
        ||| A list, starting with an a, and ending with a b; where adjacent elements
        ||| alternate between types a and b.
        ||| Equivalent to List (a, b)
        public export
        data PairList a b = Nil | (::) a (Fence b a)

%name Fence xs, ys, zs
%name PairList xs, ys, zs

mutual
    public export
    Eq a => Eq b => Eq (Fence a b) where
        x :: xs == y :: ys = x == y && xs == ys

    public export
    Eq a => Eq b => Eq (PairList a b) where
        [] == [] = True
        x :: xs == y :: ys = x == y && xs == ys
        _ == _ = False

mutual
    public export
    Ord a => Ord b => Ord (Fence a b) where
        compare (x :: xs) (y ::ys)
           = case compare x y of
                  EQ => compare xs ys
                  c => c

    public export
    Ord a => Ord b => Ord (PairList a b) where
        compare [] [] = EQ
        compare [] (x :: xs) = LT
        compare (x :: xs) [] = GT
        compare (x :: xs) (y ::ys)
           = case compare x y of
                  EQ => compare xs ys
                  c => c

mutual
    public export
    Bifunctor Fence where
        bimap f g (x :: xs) = (f x) :: (bimap g f xs)

    public export
    Bifunctor PairList where
        bimap f g [] = []
        bimap f g (x :: xs) = (f x) :: (bimap g f xs)

mutual
    public export
    Bifoldable Fence where
        bifoldr f g acc (x :: xs) = f x (bifoldr g f acc xs)

        bifoldl f g acc (x :: xs) = bifoldl g f (f acc x) xs

    public export
    Bifoldable PairList where
        bifoldr f g acc [] = acc
        bifoldr f g acc (x :: xs) = f x (bifoldr g f acc xs)

        bifoldl f g acc [] = acc
        bifoldl f g acc (x :: xs) = bifoldl g f (f acc x) xs

mutual
    public export
    Bitraversable Fence where
        bitraverse f g (x :: xs) = [| f x :: bitraverse g f xs |]

    public export
    Bitraversable PairList where
        bitraverse f g [] = [| [] |]
        bitraverse f g (x :: xs) = [| f x :: bitraverse g f xs |]

public export
Functor (Fence a) where
    map = mapSnd

mutual
    namespace Fence
        public export
        (++) : Fence a b -> Fence b a -> PairList a b
        (x :: xs) ++ ys = x :: xs ++ ys

    namespace PairListFence
        public export
        (++) : PairList a b -> Fence a b -> Fence a b
        [] ++ ys = ys
        (x :: xs) ++ ys = x :: xs ++ ys

mutual
    namespace PairList
        public export
        (++) : PairList a b -> PairList a b -> PairList a b
        [] ++ ys = ys
        (x :: xs) ++ ys = x :: xs ++ ys

    namespace FencePairList
        public export
        (++) : Fence a b -> PairList b a -> Fence a b
        (x :: xs) ++ ys = x :: xs ++ ys

||| Glue together two fences by gluing together the inner-most fence-posts
public export
Semigroup a => Semigroup (Fence a b) where
    [x] <+> (y :: ys) = (x <+> y) :: ys
    (x :: y :: xs) <+> ys = x :: y :: xs <+> ys

namespace Fence
    public export
    (+>) : Semigroup a => Fence a b -> a -> Fence a b
    [x] +> z = [x <+> z]
    x :: y :: xs +> z = x :: y :: (xs +> z)

    public export
    (<+) : Semigroup a => a -> Fence a b -> Fence a b
    x <+ y :: ys = (x <+> y) :: ys

public export
Semigroup (PairList a b) where
    (<+>) = (++)

public export
Monoid a => Monoid (Fence a b) where
    neutral = [neutral]

public export
Monoid (PairList a b) where
    neutral = []

public export
Foldable (Fence a) where
    foldr = bifoldr (flip const)
    foldl = bifoldl const

public export
singleton : a -> Fence a b
singleton x = [x]

public export
Monoid a => Applicative (Fence a) where
    pure x = [neutral, x, neutral]
    fs <*> xs = biconcatMap singleton (flip map xs) fs

public export
Monoid a => Alternative (Fence a) where
    empty = [neutral]
    xs <|> ys = xs <+> ys

public export
Monoid a => Monad (Fence a) where
    x >>= f = biconcatMap singleton f x

public export
Traversable (Fence a) where
    traverse = bitraverse pure

mutual
    namespace Fence
        public export
        forget : Fence a a -> List a
        forget (x :: xs) = x :: forget xs

    namespace PairList
        public export
        forget : PairList a a -> List a
        forget [] = []
        forget (x :: xs) = x :: forget xs

export
Show a => Show b => Show (Fence a b) where
    show xs = "[\{concat $ intersperse ", " $ forget $ bimap show show xs}]"

export
Show a => Show b => Show (PairList a b) where
    show xs = "[\{concat $ intersperse ", " $ forget $ bimap show show xs}]"
