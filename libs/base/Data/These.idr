module Data.These

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
these : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these l r lr (This a)   = l a
these l r lr (That b)   = r b
these l r lr (Both a b) = lr a b

public export
(Show a, Show b) => Show (These a b) where
  showPrec d (This x)   = showCon d "This" $ showArg x
  showPrec d (That x)   = showCon d "That" $ showArg x
  showPrec d (Both x y) = showCon d "Both" $ showArg x ++ showArg y

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
bifold : Monoid m => These m m -> m
bifold (This a)   = a
bifold (That b)   = b
bifold (Both a b) = a <+> b
