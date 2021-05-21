||| Additional functions about vectors
module Data.Vect.Extra

import Data.Vect
import Data.Fin

||| Version of `map` with access to the current position
public export
mapWithPos : (f : Fin n -> a -> b) -> Vect n a -> Vect n b
mapWithPos f [] = []
mapWithPos f (x :: xs) = f 0 x :: mapWithPos (f . FS) xs
