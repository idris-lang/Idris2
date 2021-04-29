-- Test arithmetic operations for signed integers and casts.

import Data.List
import Data.Stream

record IntType (a : Type) where
  constructor MkIntType
  name      : String
  precision : Integer
  min       : Integer
  max       : Integer

intType : String -> Integer -> IntType a
intType n p = let ma = prim__shl_Integer 1 (p - 1)
               in MkIntType n p (negate ma) (ma - 1)

int8 : IntType Int8
int8 = intType "Int8" 8

int16 : IntType Int16
int16 = intType "Int16" 16

int32 : IntType Int32
int32 = intType "Int32" 32

int64 : IntType Int64
int64 = intType "Int64" 64

int : IntType Int
int = intType "Int" 64

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

filterTailRec : (a -> Bool) -> List a -> List a
filterTailRec p = run Nil
  where run : List a -> List a -> List a
        run res [] = res
        run res (h :: t) = if p h then run (h :: res) t else run res t

-- This check does the following: For a given binary operation `op`,
-- calculate the result of applying the operation to all passed pairs
-- of integers in `pairs` and check, with the given bit size, if
-- the result is out of bounds. If it is, calculate the result
-- modulo 2^bits. This gives the reference result as an `Integer`.
--
-- Not perform the same operation with the same input but for
-- the integer type we'd like to check and cast the result back
-- to an `Integer`. Create a nice error message for every pair
-- that fails (returns an empty list if all goes well).
check :  (Num a, Cast a Integer) => Op a -> List String
check (MkOp name op opInt allowZero $ MkIntType type bits mi ma) =
  let ps = if allowZero then pairs
           else filterTailRec ((0 /=) . checkBounds . snd) pairs
   in mapMaybe failing ps

  where
    checkBounds : Integer -> Integer
    checkBounds n = if n < mi || n > ma then n `mod` (ma + 1) else n

    failing : (Integer,Integer) -> Maybe String
    failing (x,y) =
      let resInteger = opInt x y
          resMod     = checkBounds $ opInt (checkBounds x) (checkBounds y)
          resA       = cast {to = Integer} (op (fromInteger x) (fromInteger y))
       in if resA == resMod
             then Nothing
             else Just #"Error when calculating \#{show x} \#{name} \#{show y} for \#{type}: Expected \#{show resMod} but got \#{show resA} (unrounded: \#{show resInteger})"#

--------------------------------------------------------------------------------
--          Int8
--------------------------------------------------------------------------------

Show Int8 where
  show = prim__cast_Int8String

Cast Int8 Integer where
  cast = prim__cast_Int8Integer

Num Int8 where
  (+) = prim__add_Int8
  (*) = prim__mul_Int8
  fromInteger = prim__cast_IntegerInt8

Neg Int8 where
  (-)    = prim__sub_Int8
  negate = prim__sub_Int8 0

Integral Int8 where
  div = prim__div_Int8
  mod = prim__mod_Int8

--------------------------------------------------------------------------------
--          Int16
--------------------------------------------------------------------------------

Show Int16 where
  show = prim__cast_Int16String

Cast Int16 Integer where
  cast = prim__cast_Int16Integer

Num Int16 where
  (+) = prim__add_Int16
  (*) = prim__mul_Int16
  fromInteger = prim__cast_IntegerInt16

Neg Int16 where
  (-)    = prim__sub_Int16
  negate = prim__sub_Int16 0

Integral Int16 where
  div = prim__div_Int16
  mod = prim__mod_Int16

--------------------------------------------------------------------------------
--          Int32
--------------------------------------------------------------------------------

Show Int32 where
  show = prim__cast_Int32String

Cast Int32 Integer where
  cast = prim__cast_Int32Integer

Num Int32 where
  (+) = prim__add_Int32
  (*) = prim__mul_Int32
  fromInteger = prim__cast_IntegerInt32

Neg Int32 where
  (-)    = prim__sub_Int32
  negate = prim__sub_Int32 0

Integral Int32 where
  div = prim__div_Int32
  mod = prim__mod_Int32

--------------------------------------------------------------------------------
--          Int64
--------------------------------------------------------------------------------

Show Int64 where
  show = prim__cast_Int64String

Cast Int64 Integer where
  cast = prim__cast_Int64Integer

Num Int64 where
  (+) = prim__add_Int64
  (*) = prim__mul_Int64
  fromInteger = prim__cast_IntegerInt64

Neg Int64 where
  (-)    = prim__sub_Int64
  negate = prim__sub_Int64 0

Integral Int64 where
  div = prim__div_Int64
  mod = prim__mod_Int64

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
