import Data.Vect

0 pair : (Int, Int) -> Int
pair (x, y) = 1

0 pairVect : (Vect n Int, Vect m Int) -> Int
pairVect ([x, y], [z, w]) = 1
pairVect _ = 2

0 dpair : (t ** Maybe t) -> Int
dpair (Bool ** Just y) = 1
dpair _ = 2

0 dpairVect : (t ** Vect n t) -> Int
dpairVect (Bool ** [y, z]) = 1
dpairVect _ = 2
