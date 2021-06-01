module Data.Bits

import Data.DPair
import public Data.Nat

%default total

infixl 8 `shiftL`, `shiftR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

||| Utility for using bitwise operations at compile
||| time.
|||
||| ```idris example
||| the Bits8 13 `shiftL` fromNat 3
||| ```
export
fromNat :  (k : Nat)
        -> {n : Nat}
        -> {auto 0 prf : lt k n === True}
        -> Subset Nat (`LT` n)
fromNat k = Element k (ltReflectsLT k n prf)

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
  Index       = Subset Nat (`LT` 8)
  (.&.)       = prim__and_Bits8
  (.|.)       = prim__or_Bits8
  xor         = prim__xor_Bits8
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits8 x . fromInteger . cast . fst
  shiftL x    = prim__shl_Bits8 x . fromInteger . cast . fst
  complement  = xor 0xff
  oneBits     = 0xff

public export %inline
Bits Bits16 where
  Index       = Subset Nat (`LT` 16)
  (.&.)       = prim__and_Bits16
  (.|.)       = prim__or_Bits16
  xor         = prim__xor_Bits16
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits16 x . fromInteger . cast . fst
  shiftL x    = prim__shl_Bits16 x . fromInteger . cast . fst
  complement  = xor 0xffff
  oneBits     = 0xffff

public export %inline
Bits Bits32 where
  Index       = Subset Nat (`LT` 32)
  (.&.)       = prim__and_Bits32
  (.|.)       = prim__or_Bits32
  xor         = prim__xor_Bits32
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits32 x . fromInteger . cast . fst
  shiftL x    = prim__shl_Bits32 x . fromInteger . cast . fst
  complement  = xor 0xffffffff
  oneBits     = 0xffffffff

public export %inline
Bits Int where
  Index       = Subset Nat (`LT` 64)
  (.&.)       = prim__and_Int
  (.|.)       = prim__or_Int
  xor         = prim__xor_Int
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int x . cast . fst
  shiftL x    = prim__shl_Int x . cast . fst
  complement  = xor (-1)
  oneBits     = (-1)

--------------------------------------------------------------------------------
--          FiniteBits
--------------------------------------------------------------------------------

public export
interface Bits a => FiniteBits a where
  ||| Return the number of bits in values of type `t`.
  bitSize : Nat

  ||| Properly correlates `bitSize` and `Index`.
  bitsToIndex : Subset Nat (`LT` bitSize) -> Index {a}

  ||| Return the number of set bits in the argument.  This number is
  ||| known as the population count or the Hamming weight.
  popCount : a -> Nat

public export %inline
FiniteBits Bits8 where
  bitSize     = 8
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x55) + ((x0 `shiftR` fromNat 1) .&. 0x55)
        x2 = (x1 .&. 0x33) + ((x1 `shiftR` fromNat 2) .&. 0x33)
        x3 = ((x2 + (x2 `shiftR` fromNat 4)) .&. 0x0F)
     in fromInteger $ cast x3

public export %inline
FiniteBits Bits16 where
  bitSize     = 16
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x5555) + ((x0 `shiftR` fromNat 1) .&. 0x5555)
        x2 = (x1 .&. 0x3333) + ((x1 `shiftR` fromNat 2) .&. 0x3333)
        x3 = ((x2 + (x2 `shiftR` fromNat 4)) .&. 0x0F0F)
        x4 = (x3 * 0x0101) `shiftR` fromNat 8
     in fromInteger $ cast x4

public export %inline
FiniteBits Bits32 where
  bitSize     = 32
  bitsToIndex = id

  popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
    let x1 = (x0 .&. 0x55555555) + ((x0 `shiftR` fromNat 1) .&. 0x55555555)
        x2 = (x1 .&. 0x33333333) + ((x1 `shiftR` fromNat 2) .&. 0x33333333)
        x3 = ((x2 + (x2 `shiftR` fromNat 4)) .&. 0x0F0F0F0F)
        x4 = (x3 * 0x01010101) `shiftR` fromNat 24
     in fromInteger $ cast x4

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
    let x0 = x `clearBit` fromNat 63
        x1 = (x0 .&. 0x5555555555555555)
           + ((x0 `shiftR` fromNat 1) .&. 0x5555555555555555)
        x2 = (x1 .&. 0x3333333333333333)
           + ((x1 `shiftR` fromNat 2) .&. 0x3333333333333333)
        x3 = ((x2 + (x2 `shiftR` fromNat 4)) .&. 0x0F0F0F0F0F0F0F0F)
        x4 = (x3 * 0x0101010101010101) `shiftR` fromNat 56
        x5 = if x < 0 then x4 + 1 else x4
     in fromInteger $ cast x5
