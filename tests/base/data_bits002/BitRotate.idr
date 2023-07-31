import Data.Bits
import Data.List
import Data.Stream
import Data.String
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

experiment : FiniteBits a => String -> (a -> a) -> List a -> String
experiment name f vals
  = unlines
  $ replicate 72 '-'
  :: "-- \{name}"
  :: map (\ l => "\{asString l} \{asString (f l)}") vals

--------------------------------------------------------------------------------
--          rotR
--------------------------------------------------------------------------------

rotRBits8 : String
rotRBits8 = experiment "RotR Bits8" (`rotR` 1) (0 :: powsOf2 8 ++ [b8max])

rotRBits16 : String
rotRBits16 = experiment "RotR Bits16" (`rotR` 1) (0 :: powsOf2 16 ++ [b16max])

rotRBits32 : String
rotRBits32 = experiment "RotR Bits32" (`rotR` 1) (0 :: powsOf2 32 ++ [b32max])

rotRInt : String
rotRInt = experiment "RotR Int" (`rotR` 1) (0 :: powsOf2 63 ++ [intmax])

rotRNegativeInt : String
rotRNegativeInt = experiment "RotR negative Int" (`rotR` 1) (0 :: map negate (powsOf2 63) ++ [intmin])

--------------------------------------------------------------------------------
--          rotL
--------------------------------------------------------------------------------

rotLBits8 : String
rotLBits8 = experiment "RotL Bits8" (`rotL` 1) (0 :: powsOf2 8 ++ [b8max])

rotLBits16 : String
rotLBits16 = experiment "RotL Bits16" (`rotL` 1) (0 :: powsOf2 16 ++ [b16max])

rotLBits32 : String
rotLBits32 = experiment "RotL Bits32" (`rotL` 1) (0 :: powsOf2 32 ++ [b32max])

rotLInt : String
rotLInt = experiment "RotL Int" (`rotL` 1) (0 :: powsOf2 63 ++ [intmax])

rotLNegativeInt : String
rotLNegativeInt = experiment "RotL negative Int" (`rotL` 1) (0 :: map negate (powsOf2 62) ++ [intmin])

--------------------------------------------------------------------------------
--          Running Tests
--------------------------------------------------------------------------------

main : IO ()
main = do putStrLn rotRBits8
          putStrLn rotRBits16
          putStrLn rotRBits32
          putStrLn rotRInt
          putStrLn rotRNegativeInt

          putStrLn ""

          putStrLn rotLBits8
          putStrLn rotLBits16
          putStrLn rotLBits32
          putStrLn rotLInt
          putStrLn rotLNegativeInt
