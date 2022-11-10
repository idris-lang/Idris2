module Prelude.Cast

import Prelude.Basics
import Prelude.Num
import Prelude.Types

%default total

-----------
-- CASTS --
-----------

-- Casts between primitives only here.  They might be lossy.

||| Interface for transforming an instance of a data type to another type.
public export
interface Cast from to where
  constructor MkCast
  ||| Perform a (potentially lossy!) cast operation.
  ||| @ orig The original type
  cast : (orig : from) -> to

export %inline
Cast a a where
  cast = id

-- To String

export %inline
Cast Int String where
  cast = prim__cast_IntString

export %inline
Cast Integer String where
  cast = prim__cast_IntegerString

export %inline
Cast Char String where
  cast = prim__cast_CharString

export %inline
Cast Double String where
  cast = prim__cast_DoubleString

export %inline
Cast Nat String where
  cast = cast . natToInteger

export %inline
Cast Int8 String where
  cast = prim__cast_Int8String

export %inline
Cast Int16 String where
  cast = prim__cast_Int16String

export %inline
Cast Int32 String where
  cast = prim__cast_Int32String

export %inline
Cast Int64 String where
  cast = prim__cast_Int64String

export %inline
Cast Bits8 String where
  cast = prim__cast_Bits8String

export %inline
Cast Bits16 String where
  cast = prim__cast_Bits16String

export %inline
Cast Bits32 String where
  cast = prim__cast_Bits32String

export %inline
Cast Bits64 String where
  cast = prim__cast_Bits64String

-- To Integer

export %inline
Cast Int Integer where
  cast = prim__cast_IntInteger

export %inline
Cast Char Integer where
  cast = prim__cast_CharInteger

export %inline
Cast Double Integer where
  cast = prim__cast_DoubleInteger

export %inline
Cast String Integer where
  cast = prim__cast_StringInteger

export %inline
Cast Nat Integer where
  cast = natToInteger

export %inline
Cast Bits8 Integer where
  cast = prim__cast_Bits8Integer

export %inline
Cast Bits16 Integer where
  cast = prim__cast_Bits16Integer

export %inline
Cast Bits32 Integer where
  cast = prim__cast_Bits32Integer

export %inline
Cast Bits64 Integer where
  cast = prim__cast_Bits64Integer

export %inline
Cast Int8 Integer where
  cast = prim__cast_Int8Integer

export %inline
Cast Int16 Integer where
  cast = prim__cast_Int16Integer

export %inline
Cast Int32 Integer where
  cast = prim__cast_Int32Integer

export %inline
Cast Int64 Integer where
  cast = prim__cast_Int64Integer

-- To Int

export %inline
Cast Integer Int where
  cast = prim__cast_IntegerInt

export %inline
Cast Char Int where
  cast = prim__cast_CharInt

export %inline
Cast Double Int where
  cast = prim__cast_DoubleInt

export %inline
Cast String Int where
  cast = prim__cast_StringInt

export %inline
Cast Nat Int where
  cast = fromInteger . natToInteger

export %inline
Cast Bits8 Int where
  cast = prim__cast_Bits8Int

export %inline
Cast Bits16 Int where
  cast = prim__cast_Bits16Int

export %inline
Cast Bits32 Int where
  cast = prim__cast_Bits32Int

export %inline
Cast Bits64 Int where
  cast = prim__cast_Bits64Int

export %inline
Cast Int8 Int where
  cast = prim__cast_Int8Int

export %inline
Cast Int16 Int where
  cast = prim__cast_Int16Int

export %inline
Cast Int32 Int where
  cast = prim__cast_Int32Int

export %inline
Cast Int64 Int where
  cast = prim__cast_Int64Int

-- To Char

export %inline
Cast Int Char where
  cast = prim__cast_IntChar

export %inline
Cast Integer Char where
  cast = prim__cast_IntegerChar

export %inline
Cast Nat Char where
  cast = cast . natToInteger

export %inline
Cast Bits8 Char where
  cast = prim__cast_Bits8Char

export %inline
Cast Bits16 Char where
  cast = prim__cast_Bits16Char

export %inline
Cast Bits32 Char where
  cast = prim__cast_Bits32Char

export %inline
Cast Bits64 Char where
  cast = prim__cast_Bits64Char

export %inline
Cast Int8 Char where
  cast = prim__cast_Int8Char

export %inline
Cast Int16 Char where
  cast = prim__cast_Int16Char

export %inline
Cast Int32 Char where
  cast = prim__cast_Int32Char

export %inline
Cast Int64 Char where
  cast = prim__cast_Int64Char

-- To Double

export %inline
Cast Int Double where
  cast = prim__cast_IntDouble

export %inline
Cast Integer Double where
  cast = prim__cast_IntegerDouble

export %inline
Cast String Double where
  cast = prim__cast_StringDouble

export %inline
Cast Nat Double where
  cast = prim__cast_IntegerDouble . natToInteger

export %inline
Cast Bits8 Double where
  cast = prim__cast_Bits8Double

export %inline
Cast Bits16 Double where
  cast = prim__cast_Bits16Double

export %inline
Cast Bits32 Double where
  cast = prim__cast_Bits32Double

export %inline
Cast Bits64 Double where
  cast = prim__cast_Bits64Double

export %inline
Cast Int8 Double where
  cast = prim__cast_Int8Double

export %inline
Cast Int16 Double where
  cast = prim__cast_Int16Double

export %inline
Cast Int32 Double where
  cast = prim__cast_Int32Double

export %inline
Cast Int64 Double where
  cast = prim__cast_Int64Double


-- To Bits8

export %inline
Cast Int Bits8 where
  cast = prim__cast_IntBits8

export %inline
Cast Integer Bits8 where
  cast = prim__cast_IntegerBits8

export %inline
Cast Bits16 Bits8 where
  cast = prim__cast_Bits16Bits8

export %inline
Cast Bits32 Bits8 where
  cast = prim__cast_Bits32Bits8

export %inline
Cast Bits64 Bits8 where
  cast = prim__cast_Bits64Bits8

export %inline
Cast String Bits8 where
  cast = prim__cast_StringBits8

export %inline
Cast Double Bits8 where
  cast = prim__cast_DoubleBits8

export %inline
Cast Char Bits8 where
  cast = prim__cast_CharBits8

export %inline
Cast Nat Bits8 where
  cast = cast . natToInteger

export %inline
Cast Int8 Bits8 where
  cast = prim__cast_Int8Bits8

export %inline
Cast Int16 Bits8 where
  cast = prim__cast_Int16Bits8

export %inline
Cast Int32 Bits8 where
  cast = prim__cast_Int32Bits8

export %inline
Cast Int64 Bits8 where
  cast = prim__cast_Int64Bits8


-- To Bits16

export %inline
Cast Int Bits16 where
  cast = prim__cast_IntBits16

export %inline
Cast Integer Bits16 where
  cast = prim__cast_IntegerBits16

export %inline
Cast Bits8 Bits16 where
  cast = prim__cast_Bits8Bits16

export %inline
Cast Bits32 Bits16 where
  cast = prim__cast_Bits32Bits16

export %inline
Cast Bits64 Bits16 where
  cast = prim__cast_Bits64Bits16

export %inline
Cast String Bits16 where
  cast = prim__cast_StringBits16

export %inline
Cast Double Bits16 where
  cast = prim__cast_DoubleBits16

export %inline
Cast Char Bits16 where
  cast = prim__cast_CharBits16

export %inline
Cast Nat Bits16 where
  cast = cast . natToInteger

export %inline
Cast Int8 Bits16 where
  cast = prim__cast_Int8Bits16

export %inline
Cast Int16 Bits16 where
  cast = prim__cast_Int16Bits16

export %inline
Cast Int32 Bits16 where
  cast = prim__cast_Int32Bits16

export %inline
Cast Int64 Bits16 where
  cast = prim__cast_Int64Bits16


-- To Bits32

export %inline
Cast Int Bits32 where
  cast = prim__cast_IntBits32

export %inline
Cast Integer Bits32 where
  cast = prim__cast_IntegerBits32

export %inline
Cast Bits8 Bits32 where
  cast = prim__cast_Bits8Bits32

export %inline
Cast Bits16 Bits32 where
  cast = prim__cast_Bits16Bits32

export %inline
Cast Bits64 Bits32 where
  cast = prim__cast_Bits64Bits32

export %inline
Cast String Bits32 where
  cast = prim__cast_StringBits32

export %inline
Cast Double Bits32 where
  cast = prim__cast_DoubleBits32

export %inline
Cast Char Bits32 where
  cast = prim__cast_CharBits32

export %inline
Cast Nat Bits32 where
  cast = cast . natToInteger

export %inline
Cast Int8 Bits32 where
  cast = prim__cast_Int8Bits32

export %inline
Cast Int16 Bits32 where
  cast = prim__cast_Int16Bits32

export %inline
Cast Int32 Bits32 where
  cast = prim__cast_Int32Bits32

export %inline
Cast Int64 Bits32 where
  cast = prim__cast_Int64Bits32

-- To Bits64

export %inline
Cast Int Bits64 where
  cast = prim__cast_IntBits64

export %inline
Cast Integer Bits64 where
  cast = prim__cast_IntegerBits64

export %inline
Cast Bits8 Bits64 where
  cast = prim__cast_Bits8Bits64

export %inline
Cast Bits16 Bits64 where
  cast = prim__cast_Bits16Bits64

export %inline
Cast Bits32 Bits64 where
  cast = prim__cast_Bits32Bits64

export %inline
Cast String Bits64 where
  cast = prim__cast_StringBits64

export %inline
Cast Double Bits64 where
  cast = prim__cast_DoubleBits64

export %inline
Cast Char Bits64 where
  cast = prim__cast_CharBits64

export %inline
Cast Nat Bits64 where
  cast = cast . natToInteger

export %inline
Cast Int8 Bits64 where
  cast = prim__cast_Int8Bits64

export %inline
Cast Int16 Bits64 where
  cast = prim__cast_Int16Bits64

export %inline
Cast Int32 Bits64 where
  cast = prim__cast_Int32Bits64

export %inline
Cast Int64 Bits64 where
  cast = prim__cast_Int64Bits64

-- To Int8

export %inline
Cast String Int8 where
  cast = prim__cast_StringInt8

export %inline
Cast Double Int8 where
  cast = prim__cast_DoubleInt8

export %inline
Cast Char Int8 where
  cast = prim__cast_CharInt8

export %inline
Cast Int Int8 where
  cast = prim__cast_IntInt8

export %inline
Cast Integer Int8 where
  cast = prim__cast_IntegerInt8

export %inline
Cast Nat Int8 where
  cast = cast . natToInteger

export %inline
Cast Bits8 Int8 where
  cast = prim__cast_Bits8Int8

export %inline
Cast Bits16 Int8 where
  cast = prim__cast_Bits16Int8

export %inline
Cast Bits32 Int8 where
  cast = prim__cast_Bits32Int8

export %inline
Cast Bits64 Int8 where
  cast = prim__cast_Bits64Int8

export %inline
Cast Int16 Int8 where
  cast = prim__cast_Int16Int8

export %inline
Cast Int32 Int8 where
  cast = prim__cast_Int32Int8

export %inline
Cast Int64 Int8 where
  cast = prim__cast_Int64Int8

-- To Int16

export %inline
Cast String Int16 where
  cast = prim__cast_StringInt16

export %inline
Cast Double Int16 where
  cast = prim__cast_DoubleInt16

export %inline
Cast Char Int16 where
  cast = prim__cast_CharInt16

export %inline
Cast Int Int16 where
  cast = prim__cast_IntInt16

export %inline
Cast Integer Int16 where
  cast = prim__cast_IntegerInt16

export %inline
Cast Nat Int16 where
  cast = cast . natToInteger

export %inline
Cast Bits8 Int16 where
  cast = prim__cast_Bits8Int16

export %inline
Cast Bits16 Int16 where
  cast = prim__cast_Bits16Int16

export %inline
Cast Bits32 Int16 where
  cast = prim__cast_Bits32Int16

export %inline
Cast Bits64 Int16 where
  cast = prim__cast_Bits64Int16

export %inline
Cast Int8 Int16 where
  cast = prim__cast_Int8Int16

export %inline
Cast Int32 Int16 where
  cast = prim__cast_Int32Int16

export %inline
Cast Int64 Int16 where
  cast = prim__cast_Int64Int16

-- To Int32

export %inline
Cast String Int32 where
  cast = prim__cast_StringInt32

export %inline
Cast Double Int32 where
  cast = prim__cast_DoubleInt32

export %inline
Cast Char Int32 where
  cast = prim__cast_CharInt32

export %inline
Cast Int Int32 where
  cast = prim__cast_IntInt32

export %inline
Cast Integer Int32 where
  cast = prim__cast_IntegerInt32

export %inline
Cast Nat Int32 where
  cast = cast . natToInteger

export %inline
Cast Bits8 Int32 where
  cast = prim__cast_Bits8Int32

export %inline
Cast Bits16 Int32 where
  cast = prim__cast_Bits16Int32

export %inline
Cast Bits32 Int32 where
  cast = prim__cast_Bits32Int32

export %inline
Cast Bits64 Int32 where
  cast = prim__cast_Bits64Int32

export %inline
Cast Int8 Int32 where
  cast = prim__cast_Int8Int32

export %inline
Cast Int16 Int32 where
  cast = prim__cast_Int16Int32

export %inline
Cast Int64 Int32 where
  cast = prim__cast_Int64Int32

-- To Int64

export %inline
Cast String Int64 where
  cast = prim__cast_StringInt64

export %inline
Cast Double Int64 where
  cast = prim__cast_DoubleInt64

export %inline
Cast Char Int64 where
  cast = prim__cast_CharInt64

export %inline
Cast Int Int64 where
  cast = prim__cast_IntInt64

export %inline
Cast Integer Int64 where
  cast = prim__cast_IntegerInt64

export %inline
Cast Nat Int64 where
  cast = cast . natToInteger

export %inline
Cast Bits8 Int64 where
  cast = prim__cast_Bits8Int64

export %inline
Cast Bits16 Int64 where
  cast = prim__cast_Bits16Int64

export %inline
Cast Bits32 Int64 where
  cast = prim__cast_Bits32Int64

export %inline
Cast Bits64 Int64 where
  cast = prim__cast_Bits64Int64

export %inline
Cast Int8 Int64 where
  cast = prim__cast_Int8Int64

export %inline
Cast Int16 Int64 where
  cast = prim__cast_Int16Int64

export %inline
Cast Int32 Int64 where
  cast = prim__cast_Int32Int64

-- To Nat

export %inline
Cast String Nat where
  cast = integerToNat . cast

export %inline
Cast Double Nat where
  cast = integerToNat . cast

export %inline
Cast Char Nat where
  cast = integerToNat . cast {to = Integer}

export %inline
Cast Int Nat where
  cast = integerToNat . cast

export %inline
Cast Integer Nat where
  cast = integerToNat

export %inline
Cast Bits8 Nat where
  cast = integerToNat . cast {to = Integer}

export %inline
Cast Bits16 Nat where
  cast = integerToNat . cast {to = Integer}

export %inline
Cast Bits32 Nat where
  cast = integerToNat . cast {to = Integer}

export %inline
Cast Bits64 Nat where
  cast = integerToNat . cast {to = Integer}

export %inline
Cast Int8 Nat where
  cast = integerToNat . cast

export %inline
Cast Int16 Nat where
  cast = integerToNat . cast

export %inline
Cast Int32 Nat where
  cast = integerToNat . cast

export %inline
Cast Int64 Nat where
  cast = integerToNat . cast
