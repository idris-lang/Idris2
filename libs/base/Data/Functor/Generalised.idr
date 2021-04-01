module Data.Functor.Generalised

%default total

public export
interface GenFunctor n (0 m : Type -> Type) | m where
  gmap : (n a -> n b) -> m a -> m b

public export %inline
Functor m => GenFunctor Prelude.id m where
  gmap = map
