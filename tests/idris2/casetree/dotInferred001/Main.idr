import Data.Vect

0 foo : Vect n a -> Int
foo [x, y, z] = 1
foo _ = 2
