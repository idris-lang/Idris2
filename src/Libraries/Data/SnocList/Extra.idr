module Libraries.Data.SnocList.Extra

import Data.SnocList

public export
take : (n : Nat) -> (xs : Stream a) -> SnocList a
take Z xs = [<]
take (S k) (x :: xs) = take k xs :< x
