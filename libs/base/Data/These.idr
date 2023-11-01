module Data.These

import Control.Function

import Data.Zippable

%default total

public export
data These a b = This a | That b | Both a b

public export
fromEither : Either a b -> These a b
fromEither = either This That

public export
fromThis : These a b -> Maybe a
fromThis (This a) = Just a
fromThis (That _) = Nothing
fromThis (Both a _) = Just a

public export
fromThat : These a b -> Maybe b
fromThat (This _) = Nothing
fromThat (That b) = Just b
fromThat (Both _ b) = Just b

public export
fromBoth : (defaultL : Lazy a) -> (defaultR : Lazy b) -> These a b -> (a, b)
fromBoth _ y (This x)   = (x, y)
fromBoth x _ (That y)   = (x, y)
fromBoth _ _ (Both x y) = (x, y)

public export
these : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these l r lr (This a)   = l a
these l r lr (That b)   = r b
these l r lr (Both a b) = lr a b

public export
these' : (defualtL : Lazy a) -> (defaultR : Lazy b) -> (a -> b -> c) -> These a b -> c
these' _ y f (This x)   = f x y
these' x _ f (That y)   = f x y
these' _ _ f (Both x y) = f x y

public export
swap : These a b -> These b a
swap (This a)   = That a
swap (That b)   = This b
swap (Both a b) = Both b a

export
Injective This where
  injective Refl = Refl

export
Injective That where
  injective Refl = Refl

export
{x : _} -> Injective (Both x) where
  injective Refl = Refl

export
{y : _} -> Injective (`Both` y) where
  injective Refl = Refl

export
Biinjective Both where
  biinjective Refl = (Refl, Refl)

public export
(Show a, Show b) => Show (These a b) where
  showPrec d (This x)   = showCon d "This" $ showArg x
  showPrec d (That x)   = showCon d "That" $ showArg x
  showPrec d (Both x y) = showCon d "Both" $ showArg x ++ showArg y

public export
Eq a => Eq b => Eq (These a b) where
  This x   == This x'    = x == x'
  That x   == That x'    = x == x'
  Both x y == Both x' y' = x == x' && y == y'
  _ == _ = False

public export
Semigroup a => Semigroup b => Semigroup (These a b) where
  This x <+> This x'   = This $ x <+> x'
  This x <+> That y    = Both x y
  This x <+> Both x' y = Both (x <+> x') y

  That y <+> This x    = Both x y
  That y <+> That y'   = That $ y <+> y'
  That y <+> Both x y' = Both x $ y <+> y'

  Both x y <+> This x'    = Both (x <+> x') y
  Both x y <+> That y'    = Both x (y <+> y')
  Both x y <+> Both x' y' = Both (x <+> x') (y <+> y')

%inline
public export
Bifunctor These where
  bimap f g (This a)   = This (f a)
  bimap f g (That b)   = That (g b)
  bimap f g (Both a b) = Both (f a) (g b)

%inline
public export
Bifoldable These where
  bifoldr f _ acc (This a)   = f a acc
  bifoldr _ g acc (That b)   = g b acc
  bifoldr f g acc (Both a b) = f a (g b acc)

  bifoldl f _ acc (This a)   = f acc a
  bifoldl _ g acc (That b)   = g acc b
  bifoldl f g acc (Both a b) = g (f acc a) b

  binull _ = False

%inline
public export
Bitraversable These where
  bitraverse f _ (This a)   = This <$> f a
  bitraverse _ g (That b)   = That <$> g b
  bitraverse f g (Both a b) = [| Both (f a) (g b) |]

%inline
public export
Functor (These a) where
  map = mapSnd

public export
bifold : Semigroup m => These m m -> m
bifold (This a)   = a
bifold (That b)   = b
bifold (Both a b) = a <+> b

||| A right-biased applicative implementation that combines lefts with a semigroup operation
|||
||| This implementation does its best to not to lose any data from the original arguments.
public export
Semigroup a => Applicative (These a) where
  pure = That

  This e <*> That _    = This e
  This e <*> This e'   = This $ e <+> e'
  This e <*> Both e' _ = This $ e <+> e'

  That f <*> That x   = That $ f x
  That f <*> This e   = This e
  That f <*> Both e x = Both e $ f x

  Both e _ <*> This e'   = This $ e <+> e'
  Both e f <*> That x    = Both e $ f x
  Both e f <*> Both e' x = Both (e <+> e') $ f x

public export
Foldable (These a) where
  foldr _  init $ This _   = init
  foldr op init $ That x   = x `op` init
  foldr op init $ Both _ x = x `op` init

  foldl _  init $ This _   = init
  foldl op init $ That x   = init `op` x
  foldl op init $ Both _ x = init `op` x

  null $ This _   = True
  null $ That _   = False
  null $ Both _ _ = False

public export
Traversable (These a) where
  traverse _ $ This e   = pure $ This e
  traverse f $ That x   = That <$> f x
  traverse f $ Both x y = Both x <$> f y

public export
Semigroup a => Zippable (These a) where
  zipWith f  x y = [| f x y |]
  zipWith3 f x y z = [| f x y z |]

  unzipWith f (This x)   = (This x, This x)
  unzipWith f (That x)   = let (u, v) = f x in (That u, That v)
  unzipWith f (Both x y) = let (u, v) = f y in (Both x u, Both x v)

  unzipWith3 f (This x)   = (This x, This x, This x)
  unzipWith3 f (That x)   = let (u, v, w) = f x in (That u, That v, That w)
  unzipWith3 f (Both x y) = let (u, v, w) = f y in (Both x u, Both x v, Both x w)
