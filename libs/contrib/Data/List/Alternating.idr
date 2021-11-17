module Data.List.Alternating

import Data.Bifoldable
import Data.List

infixl 5 +>
infixr 5 <+

%default total

mutual
    namespace Odd
        ||| Non-empty list, starting and ending with an a, where adjacent elements alternate
        ||| between types a and b.
        ||| We can think of this type as:
        ||| - A fence, with the `a`s as fence-posts, and the `b`s as panels.
        ||| - A non-empty list of `a`s, separated by `b`s
        ||| - A list of `b`s, separated by, and surrounded by, `a`s
        ||| - The free extension of a monoid `a`, with variables in `b`
        public export
        data Odd a b = (::) a (Even b a)

    namespace Even
        ||| A list, starting with an a, and ending with a b; where adjacent elements
        ||| alternate between types a and b.
        ||| Equivalent to List (a, b)
        public export
        data Even a b = Nil | (::) a (Odd b a)

%name Odd xs, ys, zs
%name Even xs, ys, zs

mutual
    public export
    Eq a => Eq b => Eq (Odd a b) where
        x :: xs == y :: ys = x == y && assert_total (xs == ys)

    public export
    Eq a => Eq b => Eq (Even a b) where
        [] == [] = True
        x :: xs == y :: ys = x == y && xs == ys
        _ == _ = False

mutual
    public export
    Ord a => Ord b => Ord (Odd a b) where
        compare (x :: xs) (y ::ys)
           = case compare x y of
                  EQ => assert_total (compare xs ys)
                  c => c

    public export
    Ord a => Ord b => Ord (Even a b) where
        compare [] [] = EQ
        compare [] (x :: xs) = LT
        compare (x :: xs) [] = GT
        compare (x :: xs) (y ::ys)
           = case compare x y of
                  EQ => compare xs ys
                  c => c

mutual
    public export
    Bifunctor Odd where
        bimap f g (x :: xs) = (f x) :: assert_total (bimap g f xs)

    public export
    Bifunctor Even where
        bimap f g [] = []
        bimap f g (x :: xs) = (f x) :: (bimap g f xs)

mutual
    public export
    Bifoldable Odd where
        bifoldr f g acc (x :: xs) = f x (assert_total $ bifoldr g f acc xs)

        bifoldl f g acc (x :: xs) = assert_total $ bifoldl g f (f acc x) xs

    public export
    Bifoldable Even where
        bifoldr f g acc [] = acc
        bifoldr f g acc (x :: xs) = f x (bifoldr g f acc xs)

        bifoldl f g acc [] = acc
        bifoldl f g acc (x :: xs) = bifoldl g f (f acc x) xs

mutual
    public export
    Bitraversable Odd where
        bitraverse f g (x :: xs) = [| f x :: assert_total (bitraverse g f xs) |]

    public export
    Bitraversable Even where
        bitraverse f g [] = [| [] |]
        bitraverse f g (x :: xs) = [| f x :: bitraverse g f xs |]

namespace Snd
    public export
    Functor (Odd a) where
        map = mapSnd

namespace Fst
    public export
    [FstFunctor] Functor (\a => Odd a b) where
        map = mapFst

mutual
    namespace Odd
        public export
        (++) : Odd a b -> Odd b a -> Even a b
        (x :: xs) ++ ys = x :: xs ++ ys

    namespace EvenOdd
        public export
        (++) : Even a b -> Odd a b -> Odd a b
        [] ++ ys = ys
        (x :: xs) ++ ys = x :: xs ++ ys

mutual
    namespace Even
        public export
        (++) : Even a b -> Even a b -> Even a b
        [] ++ ys = ys
        (x :: xs) ++ ys = x :: xs ++ ys

    namespace OddEven
        public export
        (++) : Odd a b -> Even b a -> Odd a b
        (x :: xs) ++ ys = x :: xs ++ ys

||| The semigroup structure induced by treating Odd as the free extension of a
||| monoid `a`, with variables in `b`
public export
Semigroup a => Semigroup (Odd a b) where
    [x] <+> (y :: ys) = (x <+> y) :: ys
    (x :: y :: xs) <+> ys = x :: y :: xs <+> ys

namespace Odd
    public export
    (+>) : Semigroup a => Odd a b -> a -> Odd a b
    [x] +> z = [x <+> z]
    x :: y :: xs +> z = x :: y :: (xs +> z)

    public export
    (<+) : Semigroup a => a -> Odd a b -> Odd a b
    x <+ y :: ys = (x <+> y) :: ys

public export
Semigroup (Even a b) where
    (<+>) = (++)

public export
Monoid a => Monoid (Odd a b) where
    neutral = [neutral]

public export
Monoid (Even a b) where
    neutral = []

public export
Foldable (Odd a) where
    foldr = bifoldr (flip const)
    foldl = bifoldl const

public export
singleton : a -> Odd a b
singleton x = [x]

namespace Snd
    public export
    Monoid a => Applicative (Odd a) where
        pure x = [neutral, x, neutral]
        fs <*> xs = biconcatMap singleton (flip map xs) fs

public export
flatten : Odd (Odd a b) b -> Odd a b
flatten [x] = x
flatten (x :: y :: xs) = x ++ (y :: flatten xs)

namespace Fst
    public export
    [FstApplicative] Applicative (\a => Odd a b) using FstFunctor where
        pure x = [x]
        fs <*> xs = flatten $ bimap (flip mapFst xs) id fs

public export
Monoid a => Alternative (Odd a) where
    empty = [neutral]
    xs <|> ys = xs <+> ys

namespace Snd
    public export
    [SndMonad] Monoid a => Monad (Odd a) where
        x >>= f = assert_total $ biconcatMap singleton f x

    public export
    (>>=) : Monoid a => Odd a b -> (b -> Odd a c) -> Odd a c
    (>>=) = (>>=) @{SndMonad}

namespace Fst
    public export
    [FstMonad] Monad (\a => Odd a b) using FstApplicative where
        x >>= f = flatten $ mapFst f x
        join = flatten

    public export
    (>>=) : Odd a c -> (a -> Odd b c) -> Odd b c
    (>>=) = (>>=) @{FstMonad}

public export
Traversable (Odd a) where
    traverse = bitraverse pure

mutual
    namespace Odd
        public export
        odds : Odd a b -> List a
        odds (x :: xs) = x :: evens xs

    namespace Even
        public export
        evens : Even a b -> List b
        evens [] = []
        evens (x :: xs) = odds xs

mutual
    namespace Odd
        public export
        evens : Odd a b -> List b
        evens (x :: xs) = odds xs

    namespace Even
        public export
        odds : Even a b -> List a
        odds [] = []
        odds (x :: xs) = x :: evens xs

mutual
    namespace Odd
        public export
        forget : Odd a a -> List a
        forget (x :: xs) = x :: forget xs

    namespace Even
        public export
        forget : Even a a -> List a
        forget [] = []
        forget (x :: xs) = x :: forget xs

export
Show a => Show b => Show (Odd a b) where
    show xs = "[\{concat $ intersperse ", " $ forget $ bimap show show xs}]"

export
Show a => Show b => Show (Even a b) where
    show xs = "[\{concat $ intersperse ", " $ forget $ bimap show show xs}]"
