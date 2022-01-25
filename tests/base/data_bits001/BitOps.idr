import Data.Bits
import Data.DPair
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
--          shiftR
--------------------------------------------------------------------------------

shiftRBits8 : List Bits8
shiftRBits8 = map (`shiftR` 1) (powsOf2 8 ++ [b8max])

shiftRBits16 : List Bits16
shiftRBits16 = map (`shiftR` 1) (powsOf2 16 ++ [b16max])

shiftRBits32 : List Bits32
shiftRBits32 = map (`shiftR` 1) (powsOf2 32 ++ [b32max])

shiftRInt : List Int
shiftRInt = map (`shiftR` 1) (powsOf2 63 ++ [intmax])

shiftRNegativeInt : List Int
shiftRNegativeInt = map (`shiftR` 1) (map negate (powsOf2 63) ++ [intmin])

--------------------------------------------------------------------------------
--          shiftL
--------------------------------------------------------------------------------

shiftLBits8 : List Bits8
shiftLBits8 = map (`shiftL` 1) (0 :: powsOf2 7)

shiftLBits16 : List Bits16
shiftLBits16 = map (`shiftL` 1) (0 :: powsOf2 15)

shiftLBits32 : List Bits32
shiftLBits32 = map (`shiftL` 1) (0 :: powsOf2 31)

shiftLInt : List Int
shiftLInt = map (`shiftL` 1) (0 :: powsOf2 62)

shiftLNegativeInt : List Int
shiftLNegativeInt = map (`shiftL` 1) (map negate (powsOf2 62))


--------------------------------------------------------------------------------
--          Bitwise AND
--------------------------------------------------------------------------------

andBits8 : List Bits8
andBits8 = [ 11 .&. b8max
           , 11 .&. 0
           , 11 .&. 1
           , 11 .&. 2
           , 11 .&. 4
           , 11 .&. 11
           ]

andBits16 : List Bits16
andBits16 = [ 11 .&. b16max
            , 11 .&. 0
            , 11 .&. 1
            , 11 .&. 2
            , 11 .&. 4
            , 11 .&. 11
            ]

andBits32 : List Bits32
andBits32 = [ 11 .&. b32max
            , 11 .&. 0
            , 11 .&. 1
            , 11 .&. 2
            , 11 .&. 4
            , 11 .&. 11
            ]

andInt : List Int
andInt = [ 11 .&. intmax
         , 11 .&. 0
         , 11 .&. 1
         , 11 .&. 2
         , 11 .&. 4
         , 11 .&. 11
         ]

andNegativeInt : List Int
andNegativeInt = [ (-11) .&. intmax
                 , (-11) .&. 0
                 , (-11) .&. 1
                 , (-11) .&. 2
                 , (-11) .&. 4
                 , (-11) .&. 11
                 , (-11) .&. intmin
                 , (-11) .&. (-1)
                 , (-11) .&. (-2)
                 , (-11) .&. (-4)
                 , (-11) .&. (-11)
                 ]

--------------------------------------------------------------------------------
--          Bitwise OR
--------------------------------------------------------------------------------

orBits8 : List Bits8
orBits8 = [ 11 .|. b8max
          , 11 .|. 0
          , 11 .|. 1
          , 11 .|. 2
          , 11 .|. 4
          , 11 .|. 11
          ]

orBits16 : List Bits16
orBits16 = [ 11 .|. b16max
           , 11 .|. 0
           , 11 .|. 1
           , 11 .|. 2
           , 11 .|. 4
           , 11 .|. 11
           ]

orBits32 : List Bits32
orBits32 = [ 11 .|. b32max
           , 11 .|. 0
           , 11 .|. 1
           , 11 .|. 2
           , 11 .|. 4
           , 11 .|. 11
           ]

orInt : List Int
orInt = [ 11 .|. intmax
        , 11 .|. 0
        , 11 .|. 1
        , 11 .|. 2
        , 11 .|. 4
        , 11 .|. 11
        ]

orNegativeInt : List Int
orNegativeInt = [ (-11) .|. intmax
                , (-11) .|. 0
                , (-11) .|. 1
                , (-11) .|. 2
                , (-11) .|. 4
                , (-11) .|. 11
                , (-11) .|. intmin
                , (-11) .|. (-1)
                , (-11) .|. (-2)
                , (-11) .|. (-4)
                , (-11) .|. (-11)
                ]

--------------------------------------------------------------------------------
--          Bitwise XOR
--------------------------------------------------------------------------------

xorBits8 : List Bits8
xorBits8 = [ 11 `xor` b8max
           , 11 `xor` 0
           , 11 `xor` 1
           , 11 `xor` 2
           , 11 `xor` 4
           , 11 `xor` 11
           ]

xorBits16 : List Bits16
xorBits16 = [ 11 `xor` b16max
            , 11 `xor` 0
            , 11 `xor` 1
            , 11 `xor` 2
            , 11 `xor` 4
            , 11 `xor` 11
            ]

xorBits32 : List Bits32
xorBits32 = [ 11 `xor` b32max
            , 11 `xor` 0
            , 11 `xor` 1
            , 11 `xor` 2
            , 11 `xor` 4
            , 11 `xor` 11
            ]

xorInt : List Int
xorInt = [ 11 `xor` intmax
         , 11 `xor` 0
         , 11 `xor` 1
         , 11 `xor` 2
         , 11 `xor` 4
         , 11 `xor` 11
         ]

xorNegativeInt : List Int
xorNegativeInt = [ (-11) `xor` intmax
                 , (-11) `xor` 0
                 , (-11) `xor` 1
                 , (-11) `xor` 2
                 , (-11) `xor` 4
                 , (-11) `xor` 11
                 , (-11) `xor` intmin
                 , (-11) `xor` (-1)
                 , (-11) `xor` (-2)
                 , (-11) `xor` (-4)
                 , (-11) `xor` (-11)
                 ]

--------------------------------------------------------------------------------
--          bit
--------------------------------------------------------------------------------

bitBits8 : List Bits8
bitBits8 = map bit $ mapMaybe (`natToFin` 8) [0..7]

bitBits16 : List Bits16
bitBits16 = map bit $ mapMaybe (`natToFin` 16) [0..15]

bitBits32 : List Bits32
bitBits32 = map bit $ mapMaybe (`natToFin` 32) [0..31]

bitInt : List Int
bitInt = map bit $ mapMaybe (`natToFin` 64) [0..63]

--------------------------------------------------------------------------------
--          complementBit
--------------------------------------------------------------------------------

complementBitBits8 : List Bits8
complementBitBits8 = map (`complementBit` 1) bitBits8

complementBitBits16 : List Bits16
complementBitBits16 = map (`complementBit` 1) bitBits16

complementBitBits32 : List Bits32
complementBitBits32 = map (`complementBit` 1) bitBits32

complementBitInt : List Int
complementBitInt = map (`complementBit` 1) bitInt

--------------------------------------------------------------------------------
--          clearBit
--------------------------------------------------------------------------------

clearBitBits8 : List Bits8
clearBitBits8 = map (`clearBit` 5) bitBits8

clearBitBits16 : List Bits16
clearBitBits16 = map (`clearBit` 5) bitBits16

clearBitBits32 : List Bits32
clearBitBits32 = map (`clearBit` 5) bitBits32

clearBitInt : List Int
clearBitInt = map (`clearBit` 5) bitInt

--------------------------------------------------------------------------------
--          setBit
--------------------------------------------------------------------------------

setBitBits8 : List Bits8
setBitBits8 = map (`setBit` 1) bitBits8

setBitBits16 : List Bits16
setBitBits16 = map (`setBit` 1) bitBits16

setBitBits32 : List Bits32
setBitBits32 = map (`setBit` 1) bitBits32

setBitInt : List Int
setBitInt = map (`setBit` 1) bitInt

--------------------------------------------------------------------------------
--          testBit
--------------------------------------------------------------------------------

testBitBits8 : List Bool
testBitBits8 = map (testBit (the Bits8 0xaa))
             $ mapMaybe (`natToFin` 8) [0..7]

testBitBits16 : List Bool
testBitBits16 = map (testBit (the Bits16 0xaaaa))
              $ mapMaybe (`natToFin` 16) [0..15]

testBitBits32 : List Bool
testBitBits32 = map (testBit (the Bits32 0xaaaaaaaa))
              $ mapMaybe (`natToFin` 32) [0..31]

testBitInt : List Bool
testBitInt = map (testBit (the Int 0xaaaaaaaaaaaaaaa))
           $ mapMaybe (`natToFin` 64) [0..63]

testBitNegInt : List Bool
testBitNegInt = map (testBit (negate $ the Int 0xaaaaaaaaaaaaaaa))
              $ mapMaybe (`natToFin` 64) [0..63]

--------------------------------------------------------------------------------
--          popCount
--------------------------------------------------------------------------------

popCountBits8 : List Nat
popCountBits8 = map popCount [the Bits8 0, 0xaa, 0xff]

popCountBits16 : List Nat
popCountBits16 = map popCount [the Bits16 0, 0xaaaa, 0xffff]

popCountBits32 : List Nat
popCountBits32 = map popCount [the Bits32 0, 0xaaaaaaaa, 0xffffffff]

popCountInt : List Nat
popCountInt = map popCount [ the Int 0

                           -- 0101 0101 ... 0101
                           -- => 32
                           , 0x5555555555555555

                           , -1

                           -- 1010 1010 ... 1011
                           -- => 33
                           , negate 0x5555555555555555
                           ]

--------------------------------------------------------------------------------
--          Running Tests
--------------------------------------------------------------------------------

main : IO ()
main = do printLn shiftRBits8
          printLn shiftRBits16
          printLn shiftRBits32
          printLn shiftRInt
          printLn shiftRNegativeInt

          putStrLn ""

          printLn shiftLBits8
          printLn shiftLBits16
          printLn shiftLBits32
          printLn shiftLInt
          printLn shiftLNegativeInt

          putStrLn ""

          printLn andBits8
          printLn andBits16
          printLn andBits32
          printLn andInt
          printLn andNegativeInt

          putStrLn ""

          printLn orBits8
          printLn orBits16
          printLn orBits32
          printLn orInt
          printLn orNegativeInt

          putStrLn ""

          printLn xorBits8
          printLn xorBits16
          printLn xorBits32
          printLn xorInt
          printLn xorNegativeInt

          putStrLn ""

          printLn bitBits8
          printLn bitBits16
          printLn bitBits32
          printLn bitInt

          putStrLn ""

          printLn complementBitBits8
          printLn complementBitBits16
          printLn complementBitBits32
          printLn complementBitInt

          putStrLn ""

          printLn clearBitBits8
          printLn clearBitBits16
          printLn clearBitBits32
          printLn clearBitInt

          putStrLn ""

          printLn setBitBits8
          printLn setBitBits16
          printLn setBitBits32
          printLn setBitInt

          putStrLn ""

          printLn testBitBits8
          printLn testBitBits16
          printLn testBitBits32
          printLn testBitInt
          printLn testBitNegInt

          putStrLn ""

          printLn popCountBits8
          printLn popCountBits16
          printLn popCountBits32
          printLn popCountInt
