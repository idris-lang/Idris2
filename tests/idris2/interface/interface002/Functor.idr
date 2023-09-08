import Stuff

interface Functor f where
    map : (a -> b) -> f a -> f b

Functor List where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

data Test : Type -> Type -> Type -> Type where
     MkTest : a -> b -> c -> Test a b c

Functor (Test c d) where
  map = ?foo

-- Checking we can cope with the clash between the a,b here and the
-- a,b in 'map' (the names here get priority, and the ones in map get
-- renamed)
Functor (Test a b) where
  map = ?bar
