-- Tests bitwise ops for the different data types
--
-- The tests in `idris2/basic055`, `chez/chez032` and `node/node024` are the
-- same and should all have the same output.

import Data.Stream

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
--          shiftR
--------------------------------------------------------------------------------

shiftRBits8 : List Bits8
shiftRBits8 = map (`prim__shr_Bits8` 1) (powsOf2 8 ++ [b8max])

shiftRBits16 : List Bits16
shiftRBits16 = map (`prim__shr_Bits16` 1) (powsOf2 16 ++ [b16max])

shiftRBits32 : List Bits32
shiftRBits32 = map (`prim__shr_Bits32` 1) (powsOf2 32 ++ [b32max])

shiftRBits64 : List Bits64
shiftRBits64 = map (`prim__shr_Bits64` 1) (powsOf2 64 ++ [b64max])

shiftRInteger : List Integer
shiftRInteger = map (`prim__shr_Integer` 1) (powsOf2 128)

shiftRInt : List Int
shiftRInt = map (`prim__shr_Int` 1) (powsOf2 63 ++ [intmax])

shiftRNegativeInt : List Int
shiftRNegativeInt = map (`prim__shr_Int` 1) (map negate (powsOf2 63) ++ [intmin])

--------------------------------------------------------------------------------
--          shiftL
--------------------------------------------------------------------------------

shiftLBits8 : List Bits8
shiftLBits8 = map (`prim__shl_Bits8` 1) (0 :: powsOf2 7)

shiftLBits16 : List Bits16
shiftLBits16 = map (`prim__shl_Bits16` 1) (0 :: powsOf2 15)

shiftLBits32 : List Bits32
shiftLBits32 = map (`prim__shl_Bits32` 1) (0 :: powsOf2 31)

shiftLBits64 : List Bits64
shiftLBits64 = map (`prim__shl_Bits64` 1) (0 :: powsOf2 63)

shiftLInteger : List Integer
shiftLInteger = map (`prim__shl_Integer` 1) (0 :: powsOf2 127)

shiftLInt : List Int
shiftLInt = map (`prim__shl_Int` 1) (0 :: powsOf2 62)

shiftLNegativeInt : List Int
shiftLNegativeInt = map (`prim__shl_Int` 1) (map negate (powsOf2 62))


--------------------------------------------------------------------------------
--          Bitwise AND
--------------------------------------------------------------------------------

andBits8 : List Bits8
andBits8 = [ prim__and_Bits8 11 b8max
           , prim__and_Bits8 11 0
           , prim__and_Bits8 11 1
           , prim__and_Bits8 11 2
           , prim__and_Bits8 11 4
           , prim__and_Bits8 11 11
           ]

andBits16 : List Bits16
andBits16 = [ prim__and_Bits16 11 b16max
            , prim__and_Bits16 11 0
            , prim__and_Bits16 11 1
            , prim__and_Bits16 11 2
            , prim__and_Bits16 11 4
            , prim__and_Bits16 11 11
            ]

andBits32 : List Bits32
andBits32 = [ prim__and_Bits32 11 b32max
            , prim__and_Bits32 11 0
            , prim__and_Bits32 11 1
            , prim__and_Bits32 11 2
            , prim__and_Bits32 11 4
            , prim__and_Bits32 11 11
            ]

andBits64 : List Bits64
andBits64 = [ prim__and_Bits64 11 b64max
            , prim__and_Bits64 11 0
            , prim__and_Bits64 11 1
            , prim__and_Bits64 11 2
            , prim__and_Bits64 11 4
            , prim__and_Bits64 11 11
            ]

andInteger : List Integer
andInteger = [ prim__and_Integer 11 (prim__shl_Integer 1 128 - 1)
             , prim__and_Integer 11 0
             , prim__and_Integer 11 1
             , prim__and_Integer 11 2
             , prim__and_Integer 11 4
             , prim__and_Integer 11 11
             ]

andInt : List Int
andInt = [ prim__and_Int 11 intmax
         , prim__and_Int 11 0
         , prim__and_Int 11 1
         , prim__and_Int 11 2
         , prim__and_Int 11 4
         , prim__and_Int 11 11
         ]

andNegativeInt : List Int
andNegativeInt = [ prim__and_Int (-11) intmax
                 , prim__and_Int (-11) 0
                 , prim__and_Int (-11) 1
                 , prim__and_Int (-11) 2
                 , prim__and_Int (-11) 4
                 , prim__and_Int (-11) 11
                 , prim__and_Int (-11) intmin
                 , prim__and_Int (-11) (-1)
                 , prim__and_Int (-11) (-2)
                 , prim__and_Int (-11) (-4)
                 , prim__and_Int (-11) (-11)
                 ]

--------------------------------------------------------------------------------
--          Bitwise OR
--------------------------------------------------------------------------------

orBits8 : List Bits8
orBits8 = [ prim__or_Bits8 11 b8max
          , prim__or_Bits8 11 0
          , prim__or_Bits8 11 1
          , prim__or_Bits8 11 2
          , prim__or_Bits8 11 4
          , prim__or_Bits8 11 11
          ]

orBits16 : List Bits16
orBits16 = [ prim__or_Bits16 11 b16max
           , prim__or_Bits16 11 0
           , prim__or_Bits16 11 1
           , prim__or_Bits16 11 2
           , prim__or_Bits16 11 4
           , prim__or_Bits16 11 11
           ]

orBits32 : List Bits32
orBits32 = [ prim__or_Bits32 11 b32max
           , prim__or_Bits32 11 0
           , prim__or_Bits32 11 1
           , prim__or_Bits32 11 2
           , prim__or_Bits32 11 4
           , prim__or_Bits32 11 11
           ]

orBits64 : List Bits64
orBits64 = [ prim__or_Bits64 11 b64max
           , prim__or_Bits64 11 0
           , prim__or_Bits64 11 1
           , prim__or_Bits64 11 2
           , prim__or_Bits64 11 4
           , prim__or_Bits64 11 11
           ]

orInteger : List Integer
orInteger = [ prim__or_Integer 11 (prim__shl_Integer 1 128 - 1)
            , prim__or_Integer 11 0
            , prim__or_Integer 11 1
            , prim__or_Integer 11 2
            , prim__or_Integer 11 4
            , prim__or_Integer 11 11
            ]

orInt : List Int
orInt = [ prim__or_Int 11 intmax
        , prim__or_Int 11 0
        , prim__or_Int 11 1
        , prim__or_Int 11 2
        , prim__or_Int 11 4
        , prim__or_Int 11 11
        ]

orNegativeInt : List Int
orNegativeInt = [ prim__or_Int (-11) intmax
                , prim__or_Int (-11) 0
                , prim__or_Int (-11) 1
                , prim__or_Int (-11) 2
                , prim__or_Int (-11) 4
                , prim__or_Int (-11) 11
                , prim__or_Int (-11) intmin
                , prim__or_Int (-11) (-1)
                , prim__or_Int (-11) (-2)
                , prim__or_Int (-11) (-4)
                , prim__or_Int (-11) (-11)
                ]

--------------------------------------------------------------------------------
--          Bitwise XOR
--------------------------------------------------------------------------------

xorBits8 : List Bits8
xorBits8 = [ prim__xor_Bits8 11 b8max
           , prim__xor_Bits8 11 0
           , prim__xor_Bits8 11 1
           , prim__xor_Bits8 11 2
           , prim__xor_Bits8 11 4
           , prim__xor_Bits8 11 11
           ]

xorBits16 : List Bits16
xorBits16 = [ prim__xor_Bits16 11 b16max
            , prim__xor_Bits16 11 0
            , prim__xor_Bits16 11 1
            , prim__xor_Bits16 11 2
            , prim__xor_Bits16 11 4
            , prim__xor_Bits16 11 11
            ]

xorBits32 : List Bits32
xorBits32 = [ prim__xor_Bits32 11 b32max
            , prim__xor_Bits32 11 0
            , prim__xor_Bits32 11 1
            , prim__xor_Bits32 11 2
            , prim__xor_Bits32 11 4
            , prim__xor_Bits32 11 11
            ]

xorBits64 : List Bits64
xorBits64 = [ prim__xor_Bits64 11 b64max
            , prim__xor_Bits64 11 0
            , prim__xor_Bits64 11 1
            , prim__xor_Bits64 11 2
            , prim__xor_Bits64 11 4
            , prim__xor_Bits64 11 11
            ]

xorInteger : List Integer
xorInteger = [ prim__xor_Integer 11 (prim__shl_Integer 1 128 - 1)
             , prim__xor_Integer 11 0
             , prim__xor_Integer 11 1
             , prim__xor_Integer 11 2
             , prim__xor_Integer 11 4
             , prim__xor_Integer 11 11
             ]

xorInt : List Int
xorInt = [ prim__xor_Int 11 intmax
         , prim__xor_Int 11 0
         , prim__xor_Int 11 1
         , prim__xor_Int 11 2
         , prim__xor_Int 11 4
         , prim__xor_Int 11 11
         ]

xorNegativeInt : List Int
xorNegativeInt = [ prim__xor_Int (-11) intmax
                 , prim__xor_Int (-11) 0
                 , prim__xor_Int (-11) 1
                 , prim__xor_Int (-11) 2
                 , prim__xor_Int (-11) 4
                 , prim__xor_Int (-11) 11
                 , prim__xor_Int (-11) intmin
                 , prim__xor_Int (-11) (-1)
                 , prim__xor_Int (-11) (-2)
                 , prim__xor_Int (-11) (-4)
                 , prim__xor_Int (-11) (-11)
                 ]

--------------------------------------------------------------------------------
--          Running Tests
--------------------------------------------------------------------------------

main : IO ()
main = do printLn intmin

          putStrLn ""

          printLn shiftRBits8
          printLn shiftRBits16
          printLn shiftRBits32
          printLn shiftRBits64
          printLn shiftRInteger
          printLn shiftRInt
          printLn shiftRNegativeInt

          putStrLn ""

          printLn shiftLBits8
          printLn shiftLBits16
          printLn shiftLBits32
          printLn shiftLBits64
          printLn shiftLInteger
          printLn shiftLInt
          printLn shiftLNegativeInt

          putStrLn ""

          printLn andBits8
          printLn andBits16
          printLn andBits32
          printLn andBits64
          printLn andInteger
          printLn andInt
          printLn andNegativeInt

          putStrLn ""

          printLn orBits8
          printLn orBits16
          printLn orBits32
          printLn orBits64
          printLn orInteger
          printLn orInt
          printLn orNegativeInt

          putStrLn ""

          printLn xorBits8
          printLn xorBits16
          printLn xorBits32
          printLn xorBits64
          printLn xorInteger
          printLn xorInt
          printLn xorNegativeInt
