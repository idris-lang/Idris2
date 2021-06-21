module NatSpeedBug

import Data.Nat

v1 : Nat
v1 = 100000000

v2 : Nat
v2 = 100000000

plusNSBTest : Nat
plusNSBTest = v1 + v2

minusNSBTest : Nat
minusNSBTest = v1 `minus` v2

multNSBTest : Nat
multNSBTest = 2 * v2

natToIntegerNSBTest : Integer
natToIntegerNSBTest = natToInteger v1

integerToNatNSBTest : Nat
integerToNatNSBTest = integerToNat 100000000


main : IO ()
main = do
         putStrLn $ show plusNSBTest
         putStrLn $ show minusNSBTest
         putStrLn $ show multNSBTest
         putStrLn $ show natToIntegerNSBTest
         putStrLn $ show integerToNatNSBTest
