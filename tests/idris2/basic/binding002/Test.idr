
import Data.Vect

record Container where
  typebind constructor MkCont
  base : Type
  fibre : base -> Type

typebind
record Sigma (a : Type) (b : a -> Type) where
  constructor (*)
  p1 : a
  p2 : b p1

record Morphism (c1, c2 : Container) where
  constructor MkMor
  cont : (x : c1.base) -> Sigma (y : c2.base) | c2.fibre y -> c1.fibre x

fwd : Morphism a b -> a.base -> b.base
fwd (MkMor c) x = p1 (c x)

