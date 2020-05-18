module Control.Monad.Identity

public export
record Identity (a : Type) where
  constructor Id
  runIdentity : a

public export
Functor Identity where
    map fn (Id a) = Id (fn a)

public export
Applicative Identity where
    pure x = Id x
    (Id f) <*> (Id g) = Id (f g)

public export
Monad Identity where
    (Id x) >>= k = k x

public export
Show a => Show (Identity a) where
  showPrec d (Id x) = showCon d "Id" $ showArg x

public export
Eq a => Eq (Identity a) where
  (Id x) == (Id y) = x == y

public export
Ord a => Ord (Identity a) where
  compare (Id x) (Id y) = compare x y

-- public export
-- Enum a => Enum (Identity a) where
--   toNat (Id x) = toNat x
--   fromNat n = Id $ fromNat n
--   pred (Id n) = Id $ pred n

public export
(Semigroup a) => Semigroup (Identity a) where
  (<+>) x y = Id (runIdentity x <+> runIdentity y)

public export
(Monoid a) => Monoid (Identity a) where
  neutral = Id (neutral)
