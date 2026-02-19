import Data.Vect

0 foo : Vect n a -> Bool -> Int
foo [x, y, z] True = 1
foo [x, y, z] False = 2
foo {} = 3
