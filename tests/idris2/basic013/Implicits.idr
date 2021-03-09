public export
interface Do (0 m : Type) where
  0 Next : m -> Type
  bind : (x : m) -> Next x

-- Test that the implicits don't turn into as patterns on the LHS - they
-- shouldn't, because the elaborator hasn't got that far yet
foom : Int -> {a, b : Type} -> (a -> b) -> a -> b
foom = ?thurlingdrome

-- Similarly, for bind (we can't just implement it as >>= because of where
-- the implicits end up...)
public export
Monad m => Do (m a) where
  Next x = {b : Type} -> (a -> m b) -> m b
  bind = ?oops -- (>>=)
