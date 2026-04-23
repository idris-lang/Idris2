%default total

public export
interface FunctorB (0 k : Type) (0 t : (k -> Type) -> Type) | t where
  constructor MkFunctorB
  bmap_ : {0 f,g : k -> Type} -> ((0 a : k) -> f a -> g a) -> t f -> t g

public export
interface FunctorB k t => TraversableB k t | t where
  constructor MkTraversableB
  btraverse_ : {0 f,g : _}
    -> {auto _ : Applicative e}
    -> ((0 a : k) -> f a -> e (g a))
    -> t f -> e (t g)
