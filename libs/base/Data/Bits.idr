module Data.Bits

import public Data.Fin

%default total

infixl 8 `shiftL`, `shiftR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

--------------------------------------------------------------------------------
--          Interface Bits
--------------------------------------------------------------------------------

||| The `Bits` interface defines bitwise operations over integral types.
public export
interface Bits a where
  0 Index : Type

  ||| Bitwise "and"
  (.&.) : a -> a -> a

  ||| Bitwise "or"
  (.|.) : a -> a -> a

  ||| Bitwise "xor".
  xor : a -> a -> a

  ||| Shift the argument left by the specified number of bits.
  shiftL : a -> Index -> a

  ||| Shift the argument right by the specified number of bits.
  shiftR : a -> Index -> a

  ||| Sets the `i`-th bit.
  bit : (i : Index) -> a

  ||| The value with all bits unset.
  zeroBits : a

  ||| Returns the bitwise complement of a value.
  complement : a -> a
  complement = xor oneBits

  ||| The value with all bits set..
  oneBits : a
  oneBits = complement zeroBits

  ||| `complementBit x i` is the same as `xor x (bit i)`.
  complementBit : (x : a) -> (i : Index) -> a
  complementBit x i = x `xor` bit i

  ||| `clearBit x i` is the same as `x .&. complement (bit i)`
  clearBit : (x : a) -> (i : Index) -> a
  clearBit x i = x `xor` (bit i .&. x)

  ||| Tests, whether the i-th bit is set in the given value.
  testBit : a -> Index -> Bool

  ||| Sets the i-th bit of a value.
  setBit : a -> (i : Index) -> a
  setBit x i = x .|. bit i

public export %inline
Bits Bits8 where
  Index       = Fin 8
  (.&.)       = prim__and_Bits8
  (.|.)       = prim__or_Bits8
  xor         = prim__xor_Bits8
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits8 x . cast . finToNat
  shiftL x    = prim__shl_Bits8 x . cast . finToNat
  oneBits     = 0xff

public export %inline
Bits Bits16 where
  Index       = Fin 16
  (.&.)       = prim__and_Bits16
  (.|.)       = prim__or_Bits16
  xor         = prim__xor_Bits16
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits16 x . cast . finToNat
  shiftL x    = prim__shl_Bits16 x . cast . finToNat
  oneBits     = 0xffff

public export %inline
Bits Bits32 where
  Index       = Fin 32
  (.&.)       = prim__and_Bits32
  (.|.)       = prim__or_Bits32
  xor         = prim__xor_Bits32
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits32 x . cast . finToNat
  shiftL x    = prim__shl_Bits32 x . cast . finToNat
  oneBits     = 0xffffffff

public export %inline
Bits Bits64 where
  Index       = Fin 64
  (.&.)       = prim__and_Bits64
  (.|.)       = prim__or_Bits64
  xor         = prim__xor_Bits64
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits64 x . cast . finToNat
  shiftL x    = prim__shl_Bits64 x . cast . finToNat
  oneBits     = 0xffffffffffffffff

public export %inline
Bits Int where
  Index       = Fin 64
  (.&.)       = prim__and_Int
  (.|.)       = prim__or_Int
  xor         = prim__xor_Int
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int x . cast . finToNat
  shiftL x    = prim__shl_Int x . cast . finToNat
  oneBits     = (-1)

public export %inline
Bits Int8 where
  Index       = Fin 8
  (.&.)       = prim__and_Int8
  (.|.)       = prim__or_Int8
  xor         = prim__xor_Int8
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int8 x . cast . finToNat
  shiftL x    = prim__shl_Int8 x . cast . finToNat
  oneBits     = (-1)

public export %inline
Bits Int16 where
  Index       = Fin 16
  (.&.)       = prim__and_Int16
  (.|.)       = prim__or_Int16
  xor         = prim__xor_Int16
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int16 x . cast . finToNat
  shiftL x    = prim__shl_Int16 x . cast . finToNat
  oneBits     = (-1)

public export %inline
Bits Int32 where
  Index       = Fin 32
  (.&.)       = prim__and_Int32
  (.|.)       = prim__or_Int32
  xor         = prim__xor_Int32
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int32 x . cast . finToNat
  shiftL x    = prim__shl_Int32 x . cast . finToNat
  oneBits     = (-1)

public export %inline
Bits Int64 where
  Index       = Fin 64
  (.&.)       = prim__and_Int64
  (.|.)       = prim__or_Int64
  xor         = prim__xor_Int64
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int64 x . cast . finToNat
  shiftL x    = prim__shl_Int64 x . cast . finToNat
  oneBits     = (-1)

public export %inline
Bits Integer where
  Index       = Nat
  (.&.)       = prim__and_Integer
  (.|.)       = prim__or_Integer
  xor         = prim__xor_Integer
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Integer x . natToInteger
  shiftL x    = prim__shl_Integer x . natToInteger
  oneBits     = (-1)

--------------------------------------------------------------------------------
--          FiniteBits
--------------------------------------------------------------------------------

public export
interface Bits a => FiniteBits a where
  ||| Return the number of bits in values of type `t`.
  bitSize : Nat

  ||| Properly correlates `bitSize` and `Index`.
  bitsToIndex : Fin bitSize -> Index {a}

  ||| Return the number of set bits in the argument.  This number is
  ||| known as the population count or the Hamming weight.
  popCount : a -> Nat

public export %inline
FiniteBits Bits8 where
  bitSize     = 8
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x55) + ((x0 `shiftR` 1) .&. 0x55)
        x2 = (x1 .&. 0x33) + ((x1 `shiftR` 2) .&. 0x33)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F)
     in cast x3

public export %inline
FiniteBits Bits16 where
  bitSize     = 16
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x5555) + ((x0 `shiftR` 1) .&. 0x5555)
        x2 = (x1 .&. 0x3333) + ((x1 `shiftR` 2) .&. 0x3333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F)
        x4 = (x3 * 0x0101) `shiftR` 8
     in cast x4

public export %inline
FiniteBits Bits32 where
  bitSize     = 32
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x55555555) + ((x0 `shiftR` 1) .&. 0x55555555)
        x2 = (x1 .&. 0x33333333) + ((x1 `shiftR` 2) .&. 0x33333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F)
        x4 = (x3 * 0x01010101) `shiftR` 24
     in cast x4

public export %inline
FiniteBits Bits64 where
  bitSize     = 64
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-64-bit-integer
    let x1 = (x0 .&. 0x5555555555555555) +
             ((x0 `shiftR` 1) .&. 0x5555555555555555)
        x2 = (x1 .&. 0x3333333333333333)
             + ((x1 `shiftR` 2) .&. 0x3333333333333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F0F0F0F0F)
        x4 = (x3 * 0x0101010101010101) `shiftR` 56
     in cast x4

public export %inline
FiniteBits Int where
  bitSize     = 64
  bitsToIndex = id

  popCount x =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    -- We have to treat negative numbers separately in order to
    -- prevent overflows in the first addition.
    -- The top bit is therefore cleared and 1 is added in the end
    -- in case of a negative number
    let x0 = x `clearBit` 63
        x1 = (x0 .&. 0x5555555555555555)
           + ((x0 `shiftR` 1) .&. 0x5555555555555555)
        x2 = (x1 .&. 0x3333333333333333)
           + ((x1 `shiftR` 2) .&. 0x3333333333333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F0F0F0F0F)
        x4 = (x3 * 0x0101010101010101) `shiftR` 56
        x5 = if x < 0 then x4 + 1 else x4
     in cast x5

public export %inline
FiniteBits Int8 where
  bitSize     = 8
  bitsToIndex = id

  popCount x =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    -- We have to treat negative numbers separately in order to
    -- prevent overflows in the first addition.
    -- The top bit is therefore cleared and 1 is added in the end
    -- in case of a negative number
    let x0 = x `clearBit` 7
        x1 = (x0 .&. 0x55) + ((x0 `shiftR` 1) .&. 0x55)
        x2 = (x1 .&. 0x33) + ((x1 `shiftR` 2) .&. 0x33)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F)
        x4 = if x < 0 then x3 + 1 else x3
     in cast x4

public export %inline
FiniteBits Int16 where
  bitSize     = 16
  bitsToIndex = id

  popCount x =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    -- We have to treat negative numbers separately in order to
    -- prevent overflows in the first addition.
    -- The top bit is therefore cleared and 1 is added in the end
    -- in case of a negative number
    let x0 = x `clearBit` 15
        x1 = (x0 .&. 0x5555) + ((x0 `shiftR` 1) .&. 0x5555)
        x2 = (x1 .&. 0x3333) + ((x1 `shiftR` 2) .&. 0x3333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F)
        x4 = (x3 * 0x0101) `shiftR` 8
        x5 = if x < 0 then x4 + 1 else x4
     in cast x5

public export %inline
FiniteBits Int32 where
  bitSize     = 32
  bitsToIndex = id

  popCount x =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    -- We have to treat negative numbers separately in order to
    -- prevent overflows in the first addition.
    -- The top bit is therefore cleared and 1 is added in the end
    -- in case of a negative number
    let x0 = x `clearBit` 31
        x1 = (x0 .&. 0x55555555) + ((x0 `shiftR` 1) .&. 0x55555555)
        x2 = (x1 .&. 0x33333333) + ((x1 `shiftR` 2) .&. 0x33333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F)
        x4 = (x3 * 0x01010101) `shiftR` 24
        x5 = if x < 0 then x4 + 1 else x4
     in cast x5

public export %inline
FiniteBits Int64 where
  bitSize     = 64
  bitsToIndex = id

  popCount x =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    -- We have to treat negative numbers separately in order to
    -- prevent overflows in the first addition.
    -- The top bit is therefore cleared and 1 is added in the end
    -- in case of a negative number
    let x0 = x `clearBit` 63
        x1 = (x0 .&. 0x5555555555555555)
           + ((x0 `shiftR` 1) .&. 0x5555555555555555)
        x2 = (x1 .&. 0x3333333333333333)
           + ((x1 `shiftR` 2) .&. 0x3333333333333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F0F0F0F0F)
        x4 = (x3 * 0x0101010101010101) `shiftR` 56
        x5 = if x < 0 then x4 + 1 else x4
     in cast x5
