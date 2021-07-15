public export
interface Do (0 m : Type) where
  0 Next : (a : Type) -> (b : Type) -> m -> Type
  bind : (x : m) -> Next a b x

-- This won't actually achieve anything useful, but we're testing whether
-- it successfully typechecks and in the type of 'foo' we have the right 'a'
public export
Monad m => Do (m a) where
  Next a b x = (a -> m b) -> m b
  bind x = ?foo
