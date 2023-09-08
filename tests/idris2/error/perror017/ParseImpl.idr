import Control.Monad.Identity


interface Functor' (0 f :Type -> Type) where
  map': (a -> b) -> f a -> f b

Product' : (Type -> Type) -> (Type -> Type) -> (Type -> Type -> Type)
Product' f g = (\a, b => (f a, g b))

[prod] Functor' f => Functor' g => Functor' ((Product' f g) a)

Functor' Identity where
  map' f (Id x) = Id (f x)
