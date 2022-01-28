import Data.List using () renaming (List.snoc to Snoc.list, List.replicate to A.B.C.replicate)
import Data.Vect hiding (replicate) renaming (Vect.snoc to Snoc.vect)

%default total

namespace R

  export
  replicate : Nat -> a -> List a
  replicate Z x = []
  replicate 1 x = toList (Snoc.vect [] x)
  replicate (S n) x = list (R.replicate n x) x

test : Nat -> a -> List a
test = B.C.replicate
