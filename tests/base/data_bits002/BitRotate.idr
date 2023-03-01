import Data.Bits
import Data.List
import Data.Stream
import Decidable.Equality

import Data.Fin

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

shl1 : Int -> Int
shl1 = prim__shl_Int 1

b8max : Bits8
b8max = 0xff

b16max : Bits16
b16max = 0xffff

b32max : Bits32
b32max = 0xffffffff

b64max : Bits64
b64max = 18446744073709551615

-- the only way to create -2^63
intmin : Int
intmin = shl1 63

intmax : Int
intmax = 0x7fffffffffffffff

powsOf2 : Num a => Nat -> List a
powsOf2 n = take n (iterate (*2) 1)

--------------------------------------------------------------------------------
--          rotR
--------------------------------------------------------------------------------

rotRBits8 : List Bits8
rotRBits8 = map (`rotR` 1) (0 :: powsOf2 8 ++ [b8max])

rotRBits16 : List Bits16
rotRBits16 = map (`rotR` 1) (0 :: powsOf2 16 ++ [b16max])

rotRBits32 : List Bits32
rotRBits32 = map (`rotR` 1) (0 :: powsOf2 32 ++ [b32max])

rotRInt : List Int
rotRInt = map (`rotR` 1) (0 :: powsOf2 63 ++ [intmax])

rotRNegativeInt : List Int
rotRNegativeInt = map (`rotR` 1) (0 :: map negate (powsOf2 63) ++ [intmin])

--------------------------------------------------------------------------------
--          rotL
--------------------------------------------------------------------------------

rotLBits8 : List Bits8
rotLBits8 = map (`rotL` 1) (0 :: powsOf2 8 ++ [b8max])

rotLBits16 : List Bits16
rotLBits16 = map (`rotL` 1) (0 :: powsOf2 16 ++ [b16max])

rotLBits32 : List Bits32
rotLBits32 = map (`rotL` 1) (0 :: powsOf2 32 ++ [b32max])

rotLInt : List Int
rotLInt = map (`rotL` 1) (0 :: powsOf2 63 ++ [intmax])

rotLNegativeInt : List Int
rotLNegativeInt = map (`rotL` 1) (0 :: map negate (powsOf2 62) ++ [intmin])

--------------------------------------------------------------------------------
--          Running Tests
--------------------------------------------------------------------------------

main : IO ()
main = do printLn rotRBits8
          printLn rotRBits16
          printLn rotRBits32
          printLn rotRInt
          printLn rotRNegativeInt

          putStrLn ""

          printLn rotLBits8
          printLn rotLBits16
          printLn rotLBits32
          printLn rotLInt
          printLn rotLNegativeInt

