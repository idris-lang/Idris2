
-- this is to test that changes introduced for #2032 do not ruin other things
-- (#2032 itself is a performance issue, I don't know how to properly test for that)

import Data.Fin

ex0 : {n : Nat} -> Fin (S n)
ex0 = fromInteger 0

ex1 : {n : Nat} -> Fin (S (S (S n)))
ex1 = fromInteger 2

eq0 : (===) {a=Fin 3} (fromInteger 2) (FS (FS FZ))
eq0 = Refl

eq1 : (===) {a=Fin (S (S (S k)))} (fromInteger 2) (FS (FS FZ))
eq1 = Refl

-- this will probably show up if issue #2032 is present
-- and anybody measures the time it takes this test to run...
addFourMillion : Int -> Int
addFourMillion x = 4000000 + x

-- issue #3266
failing
  fin0 : Fin 0
  fin0 = (-1)
