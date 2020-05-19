
import Data.Fin
import Data.Vect

tail : {0 A : Type} -> {n : Nat} -> (Fin (S n) -> A) -> (Fin n -> A)
tail f = f . FS

toVect : {0 A : Type} -> {n : Nat} -> (Fin n -> A) -> Vect n A
toVect {n =   Z} _ = Nil
toVect {n = S m} f = (f FZ) :: (toVect (tail f))

record Iso a b where
  constructor MkIso
  to : a -> b
  from : b -> a
  toFrom : (y : b) -> to (from y) = y
  fromTo : (x : a) -> from (to x) = x

interface Finite t where
  card : Nat
  iso  : Iso t (Fin card)

  -- default methods

  foo : Vect card t
  foo = toVect (from iso)
