module Data.List.Lazy

%default total

-- All functions here are public export
-- because their definitions are pretty much the specification.

public export
data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : a -> Lazy (LazyList a) -> LazyList a

public export
Semigroup (LazyList a) where
  [] <+> ys = ys
  (x :: xs) <+> ys = x :: (xs <+> ys)

public export
Monoid (LazyList a) where
  neutral = []

public export
Foldable LazyList where
  foldr op nil [] = nil
  foldr op nil (x :: xs) = x `op` foldr op nil xs

  foldl op acc [] = acc
  foldl op acc (x :: xs) = foldl op (acc `op` x) xs

public export
Functor LazyList where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
Applicative LazyList where
  pure x = [x]
  fs <*> vs = concatMap (\f => map f vs) fs

public export
Alternative LazyList where
  empty = []
  (<|>) = (<+>)

public export
Monad LazyList where
  m >>= f = concatMap f m

-- There is no Traversable instance for lazy lists.
-- The result of a traversal will be a non-lazy list in general
-- (you can't delay the "effect" of an applicative functor).
public export
traverse : Applicative f => (a -> f b) -> LazyList a -> f (List b)
traverse g [] = pure []
traverse g (x :: xs) = [| g x :: traverse g xs |]

-- This function is unsafe because it asserts
-- that the seed gets smaller in every iteration
-- but the type system does not check that.
--
-- Use cautiously.
public export
unsafeUnfoldr : (b -> Maybe (a, b)) -> b -> LazyList a
unsafeUnfoldr next seed =
  case next seed of
    Nothing => []
    Just (x, seed') =>
      x :: Delay (unsafeUnfoldr next $ assert_smaller seed seed')
