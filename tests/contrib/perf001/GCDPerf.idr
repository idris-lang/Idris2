module GCDPerf

import Data.Nat
import Data.Nat.Factor

%default total

main : IO ()
main = print (fst $ gcd 10000000 2084 @{LeftIsNotZero})
