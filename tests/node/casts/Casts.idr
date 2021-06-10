--
-- Primitive casts: Specification
--
-- a. Unsigned integers
--
--    Unsigned integers with a precision of x bit have a valid
--    range of [0,2^x - 1]. When casting from another integral type of value y,
--    the value is checked for being in bounds, and if it is not, the
--    unsigned remainder modulo 2^x of y is returned.
--
--    When casting from a `Double`, the value is first truncated towards 0,
--    before applying the inbounds check and (if necessary) calculating
--    the unsigned remainder modulo 2^x.
--
--    When casting from a `String`, the value is first converted to a floating
--    point number by the backend and then truncated as described above.
--
--    Example: For `Bits8` the valid range is [0,255]. Below are some
--             example casts.
--
--               cast {from = Integer} {to = Bits8} 12   = 12
--               cast {from = Integer} {to = Bits8} 256  = 0
--               cast {from = Integer} {to = Bits8} 259  = 3
--               cast {from = Integer} {to = Bits8} (-2) = 254
--               cast {from = Double} {to = Bits8} (-12.001) = 244
--               cast {from = Double} {to = Bits8} ("-12.001") = 244
--
-- b. Signed integers
--
--    Signed integers with a precision of x bit have a valid
--    range of [-2^(x-1),2^(x-1) - 1]. When casting from another
--    integral type of value y, the unsigned remainder module 2^x
--    is calculated. If the result is >= 2^(x-1), 2^x is subtracted
--    from the result. This is the same behavior as for instance in Haskell.
--
--    When casting from a `Double`, the value is first truncated towards 0,
--    before applying the inbounds check and (if necessary) truncating
--    the value.
--
--    When casting from a `String`, the value is first converted to a floating
--    point number by the backend and then truncated as described above.
--
--    Example: For `Int8` the valid range is [-128,127]. Below are some
--             example casts.
--
--               cast {from = Integer} {to = Int8} 12   = 12
--               cast {from = Integer} {to = Int8} 256  = 0
--               cast {from = Integer} {to = Int8} 259  = 4
--               cast {from = Integer} {to = Int8} (-128) = (-128)
--               cast {from = Integer} {to = Int8} (-129) = 127
--               cast {from = Double}  {to = Int8} (-12.001) = (-12)
--               cast {from = Double}  {to = Int8} ("-12.001") = (-12)
--
-- c. Characters
--
--    Casts from all integral types to `Char` are supported. Note however,
--    that only casts in the non-surrogate range are supported, that is
--    values in the ranges [0,0xd7ff] and [0xe000,0x10ffff], or, in decimal
--    notation, [0,55295] and [57344,1114111].
--
--    All casts from integer types to `Char` are therefore submitted to a
--    bounds check, and, in case the value is out of bounds, are converted to `'\0'`.
--
--
-- Test all casts from and to integral types.
-- The `Cast` implementations in here should go to `Prelude`, once
-- a new minor version of the compiler is released.
--
-- These tests verify also that the full range of integer literals
-- is supported for every integral type.
--
-- Nothing fancy is being done here:
-- All test cases have been hand-written.

import Data.List

--------------------------------------------------------------------------------
--          Int8
--------------------------------------------------------------------------------

Show Int8 where
  show = prim__cast_Int8String

public export
Eq Int8 where
  x == y = intToBool (prim__eq_Int8 x y)

Num Int8 where
  (+) = prim__add_Int8
  (*) = prim__mul_Int8
  fromInteger = prim__cast_IntegerInt8

Neg Int8 where
  (-)    = prim__sub_Int8
  negate = prim__sub_Int8 0

Cast Int8 Bits8 where
  cast = prim__cast_Int8Bits8

Cast Int8 Bits16 where
  cast = prim__cast_Int8Bits16

Cast Int8 Bits32 where
  cast = prim__cast_Int8Bits32

Cast Int8 Bits64 where
  cast = prim__cast_Int8Bits64

Cast Int8 Int16 where
  cast = prim__cast_Int8Int16

Cast Int8 Int32 where
  cast = prim__cast_Int8Int32

Cast Int8 Int64 where
  cast = prim__cast_Int8Int64

Cast Int8 Int where
  cast = prim__cast_Int8Int

Cast Int8 Integer where
  cast = prim__cast_Int8Integer

Cast Int8 String where
  cast = prim__cast_Int8String

Cast Int8 Char where
  cast = prim__cast_Int8Char

Cast Int8 Double where
  cast = prim__cast_Int8Double

--------------------------------------------------------------------------------
--          Int16
--------------------------------------------------------------------------------

public export
Eq Int16 where
  x == y = intToBool (prim__eq_Int16 x y)

Show Int16 where
  show = prim__cast_Int16String

Num Int16 where
  (+) = prim__add_Int16
  (*) = prim__mul_Int16
  fromInteger = prim__cast_IntegerInt16

Neg Int16 where
  (-)    = prim__sub_Int16
  negate = prim__sub_Int16 0

Cast Int16 Bits8 where
  cast = prim__cast_Int16Bits8

Cast Int16 Bits16 where
  cast = prim__cast_Int16Bits16

Cast Int16 Bits32 where
  cast = prim__cast_Int16Bits32

Cast Int16 Bits64 where
  cast = prim__cast_Int16Bits64

Cast Int16 Int8 where
  cast = prim__cast_Int16Int8

Cast Int16 Int32 where
  cast = prim__cast_Int16Int32

Cast Int16 Int64 where
  cast = prim__cast_Int16Int64

Cast Int16 Int where
  cast = prim__cast_Int16Int

Cast Int16 Integer where
  cast = prim__cast_Int16Integer

Cast Int16 String where
  cast = prim__cast_Int16String

Cast Int16 Char where
  cast = prim__cast_Int16Char

Cast Int16 Double where
  cast = prim__cast_Int16Double

--------------------------------------------------------------------------------
--          Int32
--------------------------------------------------------------------------------

Show Int32 where
  show = prim__cast_Int32String

public export
Eq Int32 where
  x == y = intToBool (prim__eq_Int32 x y)

Num Int32 where
  (+) = prim__add_Int32
  (*) = prim__mul_Int32
  fromInteger = prim__cast_IntegerInt32

Neg Int32 where
  (-)    = prim__sub_Int32
  negate = prim__sub_Int32 0

Cast Int32 Bits8 where
  cast = prim__cast_Int32Bits8

Cast Int32 Bits16 where
  cast = prim__cast_Int32Bits16

Cast Int32 Bits32 where
  cast = prim__cast_Int32Bits32

Cast Int32 Bits64 where
  cast = prim__cast_Int32Bits64

Cast Int32 Int8 where
  cast = prim__cast_Int32Int8

Cast Int32 Int16 where
  cast = prim__cast_Int32Int16

Cast Int32 Int64 where
  cast = prim__cast_Int32Int64

Cast Int32 Int where
  cast = prim__cast_Int32Int

Cast Int32 Integer where
  cast = prim__cast_Int32Integer

Cast Int32 String where
  cast = prim__cast_Int32String

Cast Int32 Char where
  cast = prim__cast_Int32Char

Cast Int32 Double where
  cast = prim__cast_Int32Double

--------------------------------------------------------------------------------
--          Int64
--------------------------------------------------------------------------------

Show Int64 where
  show = prim__cast_Int64String

public export
Eq Int64 where
  x == y = intToBool (prim__eq_Int64 x y)

Num Int64 where
  (+) = prim__add_Int64
  (*) = prim__mul_Int64
  fromInteger = prim__cast_IntegerInt64

Neg Int64 where
  (-)    = prim__sub_Int64
  negate = prim__sub_Int64 0

Cast Int64 Bits8 where
  cast = prim__cast_Int64Bits8

Cast Int64 Bits16 where
  cast = prim__cast_Int64Bits16

Cast Int64 Bits32 where
  cast = prim__cast_Int64Bits32

Cast Int64 Bits64 where
  cast = prim__cast_Int64Bits64

Cast Int64 Int8 where
  cast = prim__cast_Int64Int8

Cast Int64 Int16 where
  cast = prim__cast_Int64Int16

Cast Int64 Int32 where
  cast = prim__cast_Int64Int32

Cast Int64 Int where
  cast = prim__cast_Int64Int

Cast Int64 Integer where
  cast = prim__cast_Int64Integer

Cast Int64 String where
  cast = prim__cast_Int64String

Cast Int64 Char where
  cast = prim__cast_Int64Char

Cast Int64 Double where
  cast = prim__cast_Int64Double

--------------------------------------------------------------------------------
--          Int
--------------------------------------------------------------------------------

Cast Int Int8 where
  cast = prim__cast_IntInt8

Cast Int Int16 where
  cast = prim__cast_IntInt16

Cast Int Int32 where
  cast = prim__cast_IntInt32

Cast Int Int64 where
  cast = prim__cast_IntInt64

--------------------------------------------------------------------------------
--          Integer
--------------------------------------------------------------------------------

Cast Integer Int8 where
  cast = prim__cast_IntegerInt8

Cast Integer Int16 where
  cast = prim__cast_IntegerInt16

Cast Integer Int32 where
  cast = prim__cast_IntegerInt32

Cast Integer Int64 where
  cast = prim__cast_IntegerInt64

Cast Integer Char where
  cast = prim__cast_IntegerChar

--------------------------------------------------------------------------------
--          Bits8
--------------------------------------------------------------------------------

Cast Bits8 Int8 where
  cast = prim__cast_Bits8Int8

Cast Bits8 Int16 where
  cast = prim__cast_Bits8Int16

Cast Bits8 Int32 where
  cast = prim__cast_Bits8Int32

Cast Bits8 Int64 where
  cast = prim__cast_Bits8Int64

Cast Bits8 String where
  cast = prim__cast_Bits8String

Cast Bits8 Char where
  cast = prim__cast_Bits8Char

Cast Bits8 Double where
  cast = prim__cast_Bits8Double

--------------------------------------------------------------------------------
--          Bits16
--------------------------------------------------------------------------------

Cast Bits16 Int8 where
  cast = prim__cast_Bits16Int8

Cast Bits16 Int16 where
  cast = prim__cast_Bits16Int16

Cast Bits16 Int32 where
  cast = prim__cast_Bits16Int32

Cast Bits16 Int64 where
  cast = prim__cast_Bits16Int64

Cast Bits16 String where
  cast = prim__cast_Bits16String

Cast Bits16 Char where
  cast = prim__cast_Bits16Char

Cast Bits16 Double where
  cast = prim__cast_Bits16Double

--------------------------------------------------------------------------------
--          Bits32
--------------------------------------------------------------------------------

Cast Bits32 Int8 where
  cast = prim__cast_Bits32Int8

Cast Bits32 Int16 where
  cast = prim__cast_Bits32Int16

Cast Bits32 Int32 where
  cast = prim__cast_Bits32Int32

Cast Bits32 Int64 where
  cast = prim__cast_Bits32Int64

Cast Bits32 String where
  cast = prim__cast_Bits32String

Cast Bits32 Char where
  cast = prim__cast_Bits32Char

Cast Bits32 Double where
  cast = prim__cast_Bits32Double

--------------------------------------------------------------------------------
--          Bits64
--------------------------------------------------------------------------------

Cast Bits64 Int8 where
  cast = prim__cast_Bits64Int8

Cast Bits64 Int16 where
  cast = prim__cast_Bits64Int16

Cast Bits64 Int32 where
  cast = prim__cast_Bits64Int32

Cast Bits64 Int64 where
  cast = prim__cast_Bits64Int64

Cast Bits64 String where
  cast = prim__cast_Bits64String

Cast Bits64 Char where
  cast = prim__cast_Bits64Char

Cast Bits64 Double where
  cast = prim__cast_Bits64Double

--------------------------------------------------------------------------------
--          String
--------------------------------------------------------------------------------

Cast String Bits8 where
  cast = prim__cast_StringBits8

Cast String Bits16 where
  cast = prim__cast_StringBits16

Cast String Bits32 where
  cast = prim__cast_StringBits32

Cast String Bits64 where
  cast = prim__cast_StringBits64

Cast String Int8 where
  cast = prim__cast_StringInt8

Cast String Int16 where
  cast = prim__cast_StringInt16

Cast String Int32 where
  cast = prim__cast_StringInt32

Cast String Int64 where
  cast = prim__cast_StringInt64

--------------------------------------------------------------------------------
--          Double
--------------------------------------------------------------------------------

Cast Double Bits8 where
  cast = prim__cast_DoubleBits8

Cast Double Bits16 where
  cast = prim__cast_DoubleBits16

Cast Double Bits32 where
  cast = prim__cast_DoubleBits32

Cast Double Bits64 where
  cast = prim__cast_DoubleBits64

Cast Double Int8 where
  cast = prim__cast_DoubleInt8

Cast Double Int16 where
  cast = prim__cast_DoubleInt16

Cast Double Int32 where
  cast = prim__cast_DoubleInt32

Cast Double Int64 where
  cast = prim__cast_DoubleInt64

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

showTpe : Type -> String
showTpe Bits16  = "Bits16"
showTpe Bits32  = "Bits32"
showTpe Bits64  = "Bits64"
showTpe Bits8   = "Bits8"
showTpe Char    = "Char"
showTpe Double  = "Double"
showTpe Int     = "Int"
showTpe Int16   = "Int16"
showTpe Int32   = "Int32"
showTpe Int64   = "Int64"
showTpe Int8    = "Int8"
showTpe Integer = "Integer"
showTpe String  = "String"
showTpe _       = "unknown type"

testCasts : (a: Type) -> (b : Type) -> (Cast a b, Show a, Show b, Eq b) =>
            List (a,b) -> List String
testCasts a b = mapMaybe doTest
  where doTest : (a,b) -> Maybe String
        doTest (x,y) =
          let y2 = cast {to = b} x
           in if y == y2 then Nothing
              else Just $  #"Invalid cast from \#{showTpe a} to \#{showTpe b}: "#
                        ++ #"expected \#{show y} but got \#{show y2} when casting from \#{show x}"#

maxBits8 : Bits8
maxBits8 = 0xff

maxBits16 : Bits16
maxBits16 = 0xffff

maxBits32 : Bits32
maxBits32 = 0xffffffff

maxBits64 : Bits64
maxBits64 = 0xffffffffffffffff

results : List String
results =  testCasts Int8 Int16   [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Int32   [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Int64   [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Int     [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Double  [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 String  [(-129,"127"),(-128,"-128"),(0,"0"),(127,"127"),(128,"-128")]
        ++ testCasts Int8 Integer [(-129,127),(-128,-128),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Bits8   [(-129,127),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Bits16  [(-129,127),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Bits32  [(-129,127),(0,0),(127,127),(128,-128)]
        ++ testCasts Int8 Bits64  [(-129,127),(0,0),(127,127),(128,-128)]

        ++ testCasts Int16 Int8    [(-32769,32767),(-32768,0),(0,0),(32767,-1),(32768,0)]
        ++ testCasts Int16 Int32   [(-32769,32767),(-32768,-32768),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Int64   [(-32769,32767),(-32768,-32768),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Int     [(-32769,32767),(-32768,-32768),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Double  [(-32769,32767),(-32768,-32768),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 String  [(-32769,"32767"),(-32768,"-32768"),(0,"0"),(32767,"32767"),(32768,"-32768")]
        ++ testCasts Int16 Integer [(-32769,32767),(-32768,-32768),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Bits8   [(-32769,32767),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Bits16  [(-32769,32767),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Bits32  [(-32769,32767),(0,0),(32767,32767),(32768,-32768)]
        ++ testCasts Int16 Bits64  [(-32769,32767),(0,0),(32767,32767),(32768,-32768)]

        ++ testCasts Int32 Int8    [(-2147483649,2147483647),(-2147483648,0),(0,0),(2147483647,-1),(2147483648,0)]
        ++ testCasts Int32 Int16   [(-2147483649,2147483647),(-2147483648,0),(0,0),(2147483647,-1),(2147483648,0)]
        ++ testCasts Int32 Int64   [(-2147483649,2147483647),(-2147483648,-2147483648),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Int     [(-2147483649,2147483647),(-2147483648,-2147483648),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Double  [(-2147483649,2147483647),(-2147483648,-2147483648),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 String  [(-2147483649,"2147483647"),(-2147483648,"-2147483648"),(0,"0"),(2147483647,"2147483647"),(2147483648,"-2147483648")]
        ++ testCasts Int32 Integer [(-2147483649,2147483647),(-2147483648,-2147483648),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Bits8   [(-2147483649,2147483647),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Bits16  [(-2147483649,2147483647),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Bits32  [(-2147483649,2147483647),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]
        ++ testCasts Int32 Bits64  [(-2147483649,2147483647),(0,0),(2147483647,2147483647),(2147483648,-2147483648)]

        ++ testCasts Int64 Int8    [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int64 Int16   [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int64 Int32   [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int64 Int     [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int64 Double  [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int64 String  [(-9223372036854775809,"9223372036854775807"),(-9223372036854775808,"-9223372036854775808"),(0,"0"),(9223372036854775807,"9223372036854775807"),(9223372036854775808,"-9223372036854775808")]
        ++ testCasts Int64 Integer [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int64 Bits8   [(-9223372036854775809,255),(0,0),(9223372036854775807,0xff),(9223372036854775808,0)]
        ++ testCasts Int64 Bits16  [(-9223372036854775809,65535),(0,0),(9223372036854775807,0xffff),(9223372036854775808,0)]
        ++ testCasts Int64 Bits32  [(-9223372036854775809,4294967295),(0,0),(9223372036854775807,0xffffffff),(9223372036854775808,0)]
        ++ testCasts Int64 Bits64  [(-9223372036854775809,9223372036854775807),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]

        ++ testCasts Int Int8    [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int Int16   [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int Int32   [(-9223372036854775809,9223372036854775807),(-9223372036854775808,0),(0,0),(9223372036854775807,-1),(9223372036854775808,0)]
        ++ testCasts Int Int64   [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int Double  [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int String  [(-9223372036854775809,"9223372036854775807"),(-9223372036854775808,"-9223372036854775808"),(0,"0"),(9223372036854775807,"9223372036854775807"),(9223372036854775808,"-9223372036854775808")]
        ++ testCasts Int Integer [(-9223372036854775809,9223372036854775807),(-9223372036854775808,-9223372036854775808),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]
        ++ testCasts Int Bits8   [(-9223372036854775809,255),(0,0),(9223372036854775807,0xff),(9223372036854775808,0)]
        ++ testCasts Int Bits16  [(-9223372036854775809,65535),(0,0),(9223372036854775807,0xffff),(9223372036854775808,0)]
        ++ testCasts Int Bits32  [(-9223372036854775809,4294967295),(0,0),(9223372036854775807,0xffffffff),(9223372036854775808,0)]
        ++ testCasts Int Bits64  [(-9223372036854775809,9223372036854775807),(0,0),(9223372036854775807,9223372036854775807),(9223372036854775808,-9223372036854775808)]

        ++ testCasts Integer Int8    [(-170141183460469231731687303715884105729,-1),(-170141183460469231731687303715884105728,0),(0,0),(170141183460469231731687303715884105727,-1),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Int16   [(-170141183460469231731687303715884105729,-1),(-170141183460469231731687303715884105728,0),(0,0),(170141183460469231731687303715884105727,-1),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Int32   [(-170141183460469231731687303715884105729,-1),(-170141183460469231731687303715884105728,0),(0,0),(170141183460469231731687303715884105727,-1),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Int64   [(-170141183460469231731687303715884105729,-1),(-170141183460469231731687303715884105728,0),(0,0),(170141183460469231731687303715884105727,-1),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Int     [(-170141183460469231731687303715884105729,-1),(-170141183460469231731687303715884105728,0),(0,0),(170141183460469231731687303715884105727,-1),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer String  [(-170141183460469231731687303715884105729,"-170141183460469231731687303715884105729"),(-170141183460469231731687303715884105728,"-170141183460469231731687303715884105728"),(0,"0"),(170141183460469231731687303715884105727,"170141183460469231731687303715884105727"),(170141183460469231731687303715884105728,"170141183460469231731687303715884105728")]
        ++ testCasts Integer Bits8   [(-170141183460469231731687303715884105729,maxBits8),(0,0),(170141183460469231731687303715884105727,0xff),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Bits16  [(-170141183460469231731687303715884105729,maxBits16),(0,0),(170141183460469231731687303715884105727,0xffff),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Bits32  [(-170141183460469231731687303715884105729,maxBits32),(0,0),(170141183460469231731687303715884105727,0xffffffff),(170141183460469231731687303715884105728,0)]
        ++ testCasts Integer Bits64  [(-170141183460469231731687303715884105729,maxBits64),(0,0),(170141183460469231731687303715884105727,0xffffffffffffffff),(170141183460469231731687303715884105728,0)]

        ++ testCasts Bits8 Int8    [(0,0),(255,-1),(256,0)]
        ++ testCasts Bits8 Int16   [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Int32   [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Int64   [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Int     [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Double  [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 String  [(0,"0"),(255,"255"),(256,"0")]
        ++ testCasts Bits8 Integer [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Bits16  [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Bits32  [(0,0),(255,255),(256,0)]
        ++ testCasts Bits8 Bits64  [(0,0),(255,255),(256,0)]

        ++ testCasts Bits16 Int8    [(0,0),(0xffff,-1),(0x10000,0)]
        ++ testCasts Bits16 Int16   [(0,0),(0xffff,-1),(0x10000,0)]
        ++ testCasts Bits16 Int32   [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 Int64   [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 Int     [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 Double  [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 String  [(0,"0"),(0xffff,"65535"),(0x10000,"0")]
        ++ testCasts Bits16 Integer [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 Bits8   [(0,0),(0xffff,0xff),(0x10000,0)]
        ++ testCasts Bits16 Bits32  [(0,0),(0xffff,0xffff),(0x10000,0)]
        ++ testCasts Bits16 Bits64  [(0,0),(0xffff,0xffff),(0x10000,0)]

        ++ testCasts Bits32 Int8    [(0,0),(0xffffffff,-1),(0x100000000,0)]
        ++ testCasts Bits32 Int16   [(0,0),(0xffffffff,-1),(0x100000000,0)]
        ++ testCasts Bits32 Int32   [(0,0),(0xffffffff,-1),(0x100000000,0)]
        ++ testCasts Bits32 Int64   [(0,0),(0xffffffff,0xffffffff),(0x100000000,0)]
        ++ testCasts Bits32 Int     [(0,0),(0xffffffff,0xffffffff),(0x100000000,0)]
        ++ testCasts Bits32 Double  [(0,0),(0xffffffff,0xffffffff),(0x100000000,0)]
        ++ testCasts Bits32 String  [(0,"0"),(0xffffffff,"4294967295"),(0x100000000,"0")]
        ++ testCasts Bits32 Integer [(0,0),(0xffffffff,0xffffffff),(0x100000000,0)]
        ++ testCasts Bits32 Bits8   [(0,0),(0xffffffff,0xff),(0x100000000,0)]
        ++ testCasts Bits32 Bits16  [(0,0),(0xffffffff,0xffff),(0x100000000,0)]
        ++ testCasts Bits32 Bits64  [(0,0),(0xffffffff,0xffffffff),(0x100000000,0)]

        ++ testCasts Bits64 Int8    [(0,0),(0xffffffffffffffff,-1),(0x10000000000000000,0)]
        ++ testCasts Bits64 Int16   [(0,0),(0xffffffffffffffff,-1),(0x10000000000000000,0)]
        ++ testCasts Bits64 Int32   [(0,0),(0xffffffffffffffff,-1),(0x10000000000000000,0)]
        ++ testCasts Bits64 Int64   [(0,0),(0xffffffffffffffff,-1),(0x10000000000000000,0)]
        ++ testCasts Bits64 Int     [(0,0),(0xffffffffffffffff,-1),(0x10000000000000000,0)]
        ++ testCasts Bits64 Double  [(0,0),(0xffffffffffffffff,0xffffffffffffffff),(0x10000000000000000,0)]
        ++ testCasts Bits64 String  [(0,"0"),(0xffffffffffffffff,"18446744073709551615"),(0x10000000000000000,"0")]
        ++ testCasts Bits64 Integer [(0,0),(0xffffffffffffffff,0xffffffffffffffff),(0x10000000000000000,0)]
        ++ testCasts Bits64 Bits8   [(0,0),(0xffffffffffffffff,0xff),(0x10000000000000000,0)]
        ++ testCasts Bits64 Bits16  [(0,0),(0xffffffffffffffff,0xffff),(0x10000000000000000,0)]
        ++ testCasts Bits64 Bits32  [(0,0),(0xffffffffffffffff,0xffffffff),(0x10000000000000000,0)]

        ++ testCasts String Int8    [("-129",127),("-128",-128),("0",0),("127",127), ("128",-128)]
        ++ testCasts String Int16   [("-32769",32767),("-32768",-32768),("0",0),("32767",32767), ("32768",-32768)]
        ++ testCasts String Int32   [("-2147483649",2147483647),("-2147483648",-2147483648),("0",0),("2147483647",2147483647), ("2147483648",-2147483648)]
        ++ testCasts String Int64   [("-9223372036854775809",9223372036854775807),("-9223372036854775808",-9223372036854775808),("0",0),("9223372036854775807",9223372036854775807), ("9223372036854775808",-9223372036854775808)]
        ++ testCasts String Int     [("-9223372036854775809",9223372036854775807),("-9223372036854775808",-9223372036854775808),("0",0),("9223372036854775807",9223372036854775807), ("9223372036854775808",-9223372036854775808)]
        ++ testCasts String Integer [("-170141183460469231731687303715884105728",-170141183460469231731687303715884105728),("-170141183460469231731687303715884105728",-170141183460469231731687303715884105728),("0",0),("170141183460469231731687303715884105728",170141183460469231731687303715884105728)]
        ++ testCasts String Bits8   [("0",0),("255",255), ("256",0)]
        ++ testCasts String Bits16  [("0",0),("65535",65535), ("65536",0)]
        ++ testCasts String Bits32  [("0",0),("4294967295",4294967295), ("4294967296",0)]
        ++ testCasts String Bits64  [("0",0),("18446744073709551615",18446744073709551615), ("18446744073709551616",0)]

        ++ testCasts Double Int8    [(-129.0, 127),(-128.0,-128),(-12.001,-12),(12.001,12),(127.0,127),(128.0,-128)]
        ++ testCasts Double Int16   [(-32769.0, 32767),(-32768.0,-32768),(-12.001,-12),(12.001,12),(32767.0,32767),(32768.0,-32768)]
        ++ testCasts Double Int32   [(-2147483649.0,2147483647),(-2147483648.0,-2147483648),(-12.001,-12),(12.001,12),(2147483647.0,2147483647),(2147483648.0,-2147483648)]
        ++ testCasts Double Int64   [(-9223372036854775808.0,-9223372036854775808),(-12.001,-12),(12.001,12),(9223372036854775808.0,-9223372036854775808)]
        ++ testCasts Double Int     [(-9223372036854775808.0,-9223372036854775808),(-12.001,-12),(12.001,12),(9223372036854775808.0,-9223372036854775808)]
        ++ testCasts Double Bits8   [(0.0,0),(255.0,255), (256.0,0)]
        ++ testCasts Double Bits16  [(0.0,0),(65535.0,65535), (65536.0,0)]
        ++ testCasts Double Bits32  [(0.0,0),(4294967295.0,4294967295), (4294967296.0,0)]
        ++ testCasts Double Bits64  [(0.0,0),(18446744073709551616.0,0)]

        ++ testCasts Int8 Char    [(-1, '\x0'), (80, 'P')]
        ++ testCasts Int16 Char   [(-1, '\x0'), (80, 'P')]
        ++ testCasts Int32 Char   [(-1, '\x0'), (80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]
        ++ testCasts Int64 Char   [(-1, '\x0'), (80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]
        ++ testCasts Int   Char   [(-1, '\x0'), (80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]
        ++ testCasts Bits8 Char   [(80, 'P')]
        ++ testCasts Bits16 Char  [(80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000')]
        ++ testCasts Bits32 Char  [(80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]
        ++ testCasts Bits64 Char  [(80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]
        ++ testCasts Integer Char [(-1, '\x0'), (80, 'P'), (55295, '\xd7ff'), (55296, '\x0'), (57344, '\xe000'), (1114111, '\x10ffff'), (1114112, '\x0')]

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

main : IO ()
main = traverse_ putStrLn results
