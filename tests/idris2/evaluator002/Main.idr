module Main

import Lib

test : List Int
test = accMap (1+) [1,2,3]

-- refl : Main.test = [2,3,4]
-- refl = Refl
