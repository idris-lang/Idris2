public export
interface Do (0 m : Type) where
  0 Next : m -> Type
  bind : (x : m) -> Next x

public export
Monad m => Do (m a) where
  Next x = {b : Type} -> (a -> m b) -> m b
  bind x k = x >>= k

foo : Maybe Int -> Maybe Int -> Maybe Int
foo x y
   = bind x (\x' =>
     bind y (\y' => Just (x' + y')))
