import Data.Vect
import Data.Fin

Vect_ext : (v : Vect n a) -> (w : Vect n a) -> ((i : Fin n) -> index i v = index i w)
  -> v = w

Weird : (v: Vect n a) -> v = v
Weird v =  Vect_ext ?hole0 ?hole1 ?hole2

f : Bool -> Nat
f True = 0
f True = ?help
f False = 1
