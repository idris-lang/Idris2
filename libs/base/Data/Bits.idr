module Data.Bits

import Data.DPair
import Data.Nat

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

  ||| `complementBit x i` is the same as `xor x (bit i)`.
  complementBit : (x : a) -> (i : Index) -> a
  complementBit x i = x `xor` bit i

  ||| `clearBit x i` is the same as `x .&. complement (bit i)`
  clearBit : (x : a) -> (i : Index) -> a
  clearBit x i = x `xor` (bit i .&. x)

  ||| Return the number of set bits in the argument.  This number is
  ||| known as the population count or the Hamming weight.
  popCount          : a -> Nat

  ||| Tests, whether the i-th bit is set in the given value.
  testBit : a -> Index -> Bool

  ||| Sets the i-th bit of a value.
  setBit : a -> (i : Index) -> a
  setBit x i = x .|. bit i

popCountUnsigned : (Eq a, Num a, Bits a)
                 => (zero : Index {a}) -> (one : Index {a}) -> a -> Nat
popCountUnsigned z o = run 0
  where run : Nat -> a -> Nat
        run n x = if x == 0 then n
                            else let n2 = if testBit x z then S n else n
                                  in run n2 (x `shiftR` o)

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
  popCount    = popCountUnsigned (fromNat 0) (fromNat 1)

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
  popCount    = popCountUnsigned (fromNat 0) (fromNat 1)

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
  popCount    = popCountUnsigned (fromNat 0) (fromNat 1)

--------------------------------------------------------------------------------
--          FiniteBits
--------------------------------------------------------------------------------

public export
interface Bits a => FiniteBits a where
  ||| Return the number of bits in values of type `t`.
  bitSize : Nat

  ||| Returns the bitwise complement of a value.
  complement : a -> a

public export %inline
FiniteBits Bits8 where
  bitSize     = 8
  complement  = xor 0xff

public export %inline
FiniteBits Bits16 where
  bitSize     = 16
  complement  = xor 0xffff

public export %inline
FiniteBits Bits32 where
  bitSize     = 32
  complement  = xor 0xffffffff
