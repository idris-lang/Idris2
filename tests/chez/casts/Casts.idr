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
