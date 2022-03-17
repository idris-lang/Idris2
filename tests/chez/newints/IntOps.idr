--
-- Specification
--
-- a. Unsigned integers
--
--    Unsigned integers with a precision of x bit have a valid
--    range of [0,2^x - 1]. They support all the usual arithmetic
--    operations: +,*,-,div, and mod. If the result y of an operation
--    is outside the valid range, the unsigned remainder modulo 2^x of y
--    is returned instead. The same kind of truncation happens when
--    other numeric types are cast to one of the unsigned integer
--    types.
--
--    Example: For `Bits8` the valid range is [0,255]. Below are some
--             example calculations. All numbers are considered to be of type `Bits8`
--             unless specified otherwise:
--
--               255 + 7 = 6
--               3 * 128 = 128
--               (-1)    = 255
--               7 - 10  = 253
--
-- b. Signed integers
--
--    Signed integers with a precision of x bit have a valid
--    range of [-2^(x-1),2^(x-1) - 1]. They support all the usual arithmetic
--    operations: +,*,-,div, and mod. If the result `y` of an operation
--    is outside the valid range, the signed remainder modulo 2^x of `y`
--    is calculated and 2^x subtracted from the result if it
--    is still out of bounds. The same kind of truncation happens when
--    other numeric types are cast to one of the signed integer
--    types.
--
--    Example: For `Int8` the valid range is [-128,127]. Below are some
--             example calculations. All numbers are considered to be of type `Int8`
--             unless specified otherwise:
--
--               127 + 7   = -122
--               3 * 64    = -64
--               2 * (-64) = -128
--               (-129)    = 127
--               7 - 10    = -3
--
import Data.List
import Data.Stream

record IntType (a : Type) where
  constructor MkIntType
  name      : String
  signed    : Bool
  precision : Integer
  min       : Integer
  max       : Integer

intType : Bool -> String -> Integer -> IntType a
intType True  n p = let ma = prim__shl_Integer 1 (p - 1)
                     in MkIntType n True p (negate ma) (ma - 1)
intType False n p = let ma = prim__shl_Integer 1 p
                     in MkIntType n False p 0 (ma - 1)

bits8 : IntType Bits8
bits8 = intType False "Bits8" 8

bits16 : IntType Bits16
bits16 = intType False "Bits16" 16

bits32 : IntType Bits32
bits32 = intType False "Bits32" 32

bits64 : IntType Bits64
bits64 = intType False "Bits64" 64

int8 : IntType Int8
int8 = intType True "Int8" 8

int16 : IntType Int16
int16 = intType True "Int16" 16

int32 : IntType Int32
int32 = intType True "Int32" 32

int64 : IntType Int64
int64 = intType True "Int64" 64

int : IntType Int
int = intType True "Int" 64

record Op a where
  constructor MkOp
  name      : String
  op        : a -> a -> a
  opInt     : Integer -> Integer -> Integer
  allowZero : Bool
  type      : IntType a

add : Num a => IntType a -> Op a
add = MkOp "+" (+) (+) True

sub : Neg a => IntType a -> Op a
sub = MkOp "-" (-) (-) True

mul : Num a => IntType a -> Op a
mul = MkOp "*" (*) (*) True

div : Integral a => IntType a -> Op a
div = MkOp "div" (div) (div) False

mod : Integral a => IntType a -> Op a
mod = MkOp "mod" (mod) (mod) False


pairs : List (Integer,Integer)
pairs = let -- [1,2,4,8,16,...,18446744073709551616]
            powsOf2  = take 65 (iterate (*2) 1)

            -- powsOf2 ++ [0,1,3,7,...,18446744073709551615]
            naturals = powsOf2 ++ map (\x => x-1) powsOf2

            -- positive and negative versions of naturals
            ints     = naturals ++ map negate naturals

            -- naturals paired with ints
         in [| (,) ints naturals |]

-- This check does the following: For a given binary operation `op`,
-- calculate the result of applying the operation to all passed pairs
-- of integers in `pairs` and check, with the given bit size, if
-- the result is out of bounds. If it is, calculate the result
-- modulo 2^bits. This gives the reference result as an `Integer`.
--
-- Now perform the same operation with the same input but for
-- the integer type we'd like to check and cast the result back
-- to an `Integer`. Create a nice error message for every pair
-- that fails (returns an empty list if all goes well).
check :  (Num a, Cast a Integer) => Op a -> List String
check (MkOp name op opInt allowZero $ MkIntType type signed bits mi ma) =
  let ps = if allowZero then pairs
           else filter ((0 /=) . checkBounds . snd) pairs
   in mapMaybe fail ps

  where
    trueMod : Integer -> Integer -> Integer
    trueMod x y = let res = x `mod` y
                   in if res < 0 then res + y else res

    checkBounds : Integer -> Integer
    checkBounds n = let r1 = trueMod n (ma + 1 - mi)
                     in if r1 > ma
                           then r1 - (ma + 1 - mi)
                           else r1

    fail : (Integer,Integer) -> Maybe String
    fail (x,y) =
      let resInteger = opInt x y
          resMod     = checkBounds $ opInt (checkBounds x) (checkBounds y)
          resA       = cast {to = Integer} (op (fromInteger x) (fromInteger y))
       in if resA == resMod
             then Nothing
             else Just #"Error when calculating \#{show x} \#{name} \#{show y} for \#{type}: Expected \#{show resMod} but got \#{show resA} (unrounded: \#{show resInteger})"#

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

main : IO ()
main = do traverse_ putStrLn . check $ add int8
          traverse_ putStrLn . check $ sub int8
          traverse_ putStrLn . check $ mul int8
          traverse_ putStrLn . check $ div int8
          traverse_ putStrLn . check $ mod int8

          traverse_ putStrLn . check $ add int16
          traverse_ putStrLn . check $ sub int16
          traverse_ putStrLn . check $ mul int16
          traverse_ putStrLn . check $ div int16
          traverse_ putStrLn . check $ mod int16

          traverse_ putStrLn . check $ add int32
          traverse_ putStrLn . check $ sub int32
          traverse_ putStrLn . check $ mul int32
          traverse_ putStrLn . check $ div int32
          traverse_ putStrLn . check $ mod int32

          traverse_ putStrLn . check $ add int64
          traverse_ putStrLn . check $ sub int64
          traverse_ putStrLn . check $ mul int64
          traverse_ putStrLn . check $ div int64
          traverse_ putStrLn . check $ mod int64

          traverse_ putStrLn . check $ add int
          traverse_ putStrLn . check $ sub int
          traverse_ putStrLn . check $ mul int
          traverse_ putStrLn . check $ div int
          traverse_ putStrLn . check $ mod int

          traverse_ putStrLn . check $ add bits8
          traverse_ putStrLn . check $ sub bits8
          traverse_ putStrLn . check $ mul bits8
          traverse_ putStrLn . check $ div bits8
          traverse_ putStrLn . check $ mod bits8

          traverse_ putStrLn . check $ add bits16
          traverse_ putStrLn . check $ sub bits16
          traverse_ putStrLn . check $ mul bits16
          traverse_ putStrLn . check $ div bits16
          traverse_ putStrLn . check $ mod bits16

          traverse_ putStrLn . check $ add bits32
          traverse_ putStrLn . check $ sub bits32
          traverse_ putStrLn . check $ mul bits32
          traverse_ putStrLn . check $ div bits32
          traverse_ putStrLn . check $ mod bits32

          traverse_ putStrLn . check $ add bits64
          traverse_ putStrLn . check $ sub bits64
          traverse_ putStrLn . check $ mul bits64
          traverse_ putStrLn . check $ div bits64
          traverse_ putStrLn . check $ mod bits64
