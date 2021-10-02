module HVect

import Data.Vect
import Data.Vect.Elem

data HVect : Vect k Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t :: ts)

-- We wouldn't actually write it this way, but this does allow us to test
-- that delaying auto search for linear targets works.
get : (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> t
get (x :: xs) {p = Here} = x
get (x :: xs) {p = (There p')} = get xs -- {p = ?wat}
