module IntBits

import IntCasts
import IntEqOrd
import IntNum

import Data.Bits
import Data.DPair

-- This file to be deleted once these interfaces are added to base

public export %inline
Bits Int8 where
  Index       = Subset Nat (`LT` 8)
  (.&.)       = prim__and_Int8
  (.|.)       = prim__or_Int8
  xor         = prim__xor_Int8
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int8 x . cast . fst
  shiftL x    = prim__shl_Int8 x . cast . fst
  complement  = xor (-1)
  oneBits     = -1

public export %inline
Bits Int16 where
  Index       = Subset Nat (`LT` 16)
  (.&.)       = prim__and_Int16
  (.|.)       = prim__or_Int16
  xor         = prim__xor_Int16
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int16 x . cast . fst
  shiftL x    = prim__shl_Int16 x . cast . fst
  complement  = xor (-1)
  oneBits     = -1

public export %inline
Bits Int32 where
  Index       = Subset Nat (`LT` 32)
  (.&.)       = prim__and_Int32
  (.|.)       = prim__or_Int32
  xor         = prim__xor_Int32
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int32 x . cast . fst
  shiftL x    = prim__shl_Int32 x . cast . fst
  complement  = xor (-1)
  oneBits     = -1

public export %inline
Bits Int64 where
  Index       = Subset Nat (`LT` 64)
  (.&.)       = prim__and_Int64
  (.|.)       = prim__or_Int64
  xor         = prim__xor_Int64
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Int64 x . cast . fst
  shiftL x    = prim__shl_Int64 x . cast . fst
  complement  = xor (-1)
  oneBits     = -1

public export %inline
Bits Bits64 where
  Index       = Subset Nat (`LT` 64)
  (.&.)       = prim__and_Bits64
  (.|.)       = prim__or_Bits64
  xor         = prim__xor_Bits64
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Bits64 x . fromInteger . cast . fst
  shiftL x    = prim__shl_Bits64 x . fromInteger . cast . fst
  complement  = xor 0xffffffffffffffff
  oneBits     = 0xffffffffffffffff

public export %inline
Bits Integer where
  Index       = Nat
  (.&.)       = prim__and_Integer
  (.|.)       = prim__or_Integer
  xor         = prim__xor_Integer
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = (x .&. bit i) /= 0
  shiftR x    = prim__shr_Integer x . cast
  shiftL x    = prim__shl_Integer x . cast
  complement  = xor (-1)
  oneBits     = (-1)
