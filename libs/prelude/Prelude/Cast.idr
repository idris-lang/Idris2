module Prelude.Cast

import Builtin
import Prelude.Basics
import Prelude.Num
import Prelude.Types

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

export
Cast a a where
  cast = id

-- To String

export
Cast Int String where
  cast = prim__cast_IntString

export
Cast Int8 String where
  cast = prim__cast_Int8String

export
Cast Int16 String where
  cast = prim__cast_Int16String

export
Cast Int32 String where
  cast = prim__cast_Int32String

export
Cast Int64 String where
  cast = prim__cast_Int64String

export
Cast Integer String where
  cast = prim__cast_IntegerString

export
Cast Char String where
  cast = prim__cast_CharString

export
Cast Double String where
  cast = prim__cast_DoubleString

-- To Integer

export
Cast Int Integer where
  cast = prim__cast_IntInteger

export
Cast Int8 Integer where
  cast = prim__cast_Int8Integer

export
Cast Int16 Integer where
  cast = prim__cast_Int16Integer

export
Cast Int32 Integer where
  cast = prim__cast_Int32Integer

export
Cast Int64 Integer where
  cast = prim__cast_Int64Integer

export
Cast Char Integer where
  cast = prim__cast_CharInteger

export
Cast Double Integer where
  cast = prim__cast_DoubleInteger

export
Cast String Integer where
  cast = prim__cast_StringInteger

export
Cast Nat Integer where
  cast = natToInteger

export
Cast Bits8 Integer where
  cast = prim__cast_Bits8Integer

export
Cast Bits16 Integer where
  cast = prim__cast_Bits16Integer

export
Cast Bits32 Integer where
  cast = prim__cast_Bits32Integer

export
Cast Bits64 Integer where
  cast = prim__cast_Bits64Integer

-- To Int

export
Cast Int8 Int where
  cast = prim__cast_Int8Int

export
Cast Int16 Int where
  cast = prim__cast_Int16Int

export
Cast Int32 Int where
  cast = prim__cast_Int32Int

export
Cast Int64 Int where
  cast = prim__cast_Int64Int

export
Cast Integer Int where
  cast = prim__cast_IntegerInt

export
Cast Char Int where
  cast = prim__cast_CharInt

export
Cast Double Int where
  cast = prim__cast_DoubleInt

export
Cast String Int where
  cast = prim__cast_StringInt

export
Cast Nat Int where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int where
  cast = prim__cast_Bits8Int

export
Cast Bits16 Int where
  cast = prim__cast_Bits16Int

export
Cast Bits32 Int where
  cast = prim__cast_Bits32Int

export
Cast Bits64 Int where
  cast = prim__cast_Bits64Int

-- To Int8

export
Cast Int Int8 where
  cast = prim__cast_IntInt8

export
Cast Int16 Int8 where
  cast = prim__cast_Int16Int8

export
Cast Int32 Int8 where
  cast = prim__cast_Int32Int8

export
Cast Int64 Int8 where
  cast = prim__cast_Int64Int8

export
Cast Integer Int8 where
  cast = prim__cast_IntegerInt8

export
Cast Char Int8 where
  cast = prim__cast_CharInt8

export
Cast Double Int8 where
  cast = prim__cast_DoubleInt8

export
Cast String Int8 where
  cast = prim__cast_StringInt8

export
Cast Nat Int8 where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int8 where
  cast = prim__cast_Bits8Int8

export
Cast Bits16 Int8 where
  cast = prim__cast_Bits16Int8

export
Cast Bits32 Int8 where
  cast = prim__cast_Bits32Int8

export
Cast Bits64 Int8 where
  cast = prim__cast_Bits64Int8

-- To Int16

export
Cast Int Int16 where
  cast = prim__cast_IntInt16

export
Cast Int8 Int16 where
  cast = prim__cast_Int8Int16

export
Cast Int32 Int16 where
  cast = prim__cast_Int32Int16

export
Cast Int64 Int16 where
  cast = prim__cast_Int64Int16

export
Cast Integer Int16 where
  cast = prim__cast_IntegerInt16

export
Cast Char Int16 where
  cast = prim__cast_CharInt16

export
Cast Double Int16 where
  cast = prim__cast_DoubleInt16

export
Cast String Int16 where
  cast = prim__cast_StringInt16

export
Cast Nat Int16 where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int16 where
  cast = prim__cast_Bits8Int16

export
Cast Bits16 Int16 where
  cast = prim__cast_Bits16Int16

export
Cast Bits32 Int16 where
  cast = prim__cast_Bits32Int16

export
Cast Bits64 Int16 where
  cast = prim__cast_Bits64Int16

-- To Int32

export
Cast Int Int32 where
  cast = prim__cast_IntInt32

export
Cast Int8 Int32 where
  cast = prim__cast_Int8Int32

export
Cast Int16 Int32 where
  cast = prim__cast_Int16Int32

export
Cast Int64 Int32 where
  cast = prim__cast_Int64Int32

export
Cast Integer Int32 where
  cast = prim__cast_IntegerInt32

export
Cast Char Int32 where
  cast = prim__cast_CharInt32

export
Cast Double Int32 where
  cast = prim__cast_DoubleInt32

export
Cast String Int32 where
  cast = prim__cast_StringInt32

export
Cast Nat Int32 where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int32 where
  cast = prim__cast_Bits8Int32

export
Cast Bits16 Int32 where
  cast = prim__cast_Bits16Int32

export
Cast Bits32 Int32 where
  cast = prim__cast_Bits32Int32

export
Cast Bits64 Int32 where
  cast = prim__cast_Bits64Int32

-- To Int64

export
Cast Int Int64 where
  cast = prim__cast_IntInt64

export
Cast Int8 Int64 where
  cast = prim__cast_Int8Int64

export
Cast Int16 Int64 where
  cast = prim__cast_Int16Int64

export
Cast Int32 Int64 where
  cast = prim__cast_Int32Int64

export
Cast Integer Int64 where
  cast = prim__cast_IntegerInt64

export
Cast Char Int64 where
  cast = prim__cast_CharInt64

export
Cast Double Int64 where
  cast = prim__cast_DoubleInt64

export
Cast String Int64 where
  cast = prim__cast_StringInt64

export
Cast Nat Int64 where
  cast = fromInteger . natToInteger

export
Cast Bits8 Int64 where
  cast = prim__cast_Bits8Int64

export
Cast Bits16 Int64 where
  cast = prim__cast_Bits16Int64

export
Cast Bits32 Int64 where
  cast = prim__cast_Bits32Int64

export
Cast Bits64 Int64 where
  cast = prim__cast_Bits64Int64

-- To Char

export
Cast Int Char where
  cast = prim__cast_IntChar

export
Cast Int8 Char where
  cast = prim__cast_Int8Char

export
Cast Int16 Char where
  cast = prim__cast_Int16Char

export
Cast Int32 Char where
  cast = prim__cast_Int32Char

export
Cast Int64 Char where
  cast = prim__cast_Int64Char

-- To Double

export
Cast Int Double where
  cast = prim__cast_IntDouble

export
Cast Int8 Double where
  cast = prim__cast_Int8Double

export
Cast Int16 Double where
  cast = prim__cast_Int16Double

export
Cast Int32 Double where
  cast = prim__cast_Int32Double

export
Cast Int64 Double where
  cast = prim__cast_Int64Double

export
Cast Integer Double where
  cast = prim__cast_IntegerDouble

export
Cast String Double where
  cast = prim__cast_StringDouble

export
Cast Nat Double where
  cast = prim__cast_IntegerDouble . natToInteger


-- To Bits8

export
Cast Int Bits8 where
  cast = prim__cast_IntBits8

export
Cast Int8 Bits8 where
  cast = prim__cast_Int8Bits8

export
Cast Int16 Bits8 where
  cast = prim__cast_Int16Bits8

export
Cast Int32 Bits8 where
  cast = prim__cast_Int32Bits8

export
Cast Int64 Bits8 where
  cast = prim__cast_Int64Bits8

export
Cast Integer Bits8 where
  cast = prim__cast_IntegerBits8

export
Cast Bits16 Bits8 where
  cast = prim__cast_Bits16Bits8

export
Cast Bits32 Bits8 where
  cast = prim__cast_Bits32Bits8

export
Cast Bits64 Bits8 where
  cast = prim__cast_Bits64Bits8


-- To Bits16

export
Cast Int Bits16 where
  cast = prim__cast_IntBits16

export
Cast Int8 Bits16 where
  cast = prim__cast_Int8Bits16

export
Cast Int16 Bits16 where
  cast = prim__cast_Int16Bits16

export
Cast Int32 Bits16 where
  cast = prim__cast_Int32Bits16

export
Cast Int64 Bits16 where
  cast = prim__cast_Int64Bits16

export
Cast Integer Bits16 where
  cast = prim__cast_IntegerBits16

export
Cast Bits8 Bits16 where
  cast = prim__cast_Bits8Bits16

export
Cast Bits32 Bits16 where
  cast = prim__cast_Bits32Bits16

export
Cast Bits64 Bits16 where
  cast = prim__cast_Bits64Bits16


-- To Bits32

export
Cast Int Bits32 where
  cast = prim__cast_IntBits32

export
Cast Int8 Bits32 where
  cast = prim__cast_Int8Bits32

export
Cast Int16 Bits32 where
  cast = prim__cast_Int16Bits32

export
Cast Int32 Bits32 where
  cast = prim__cast_Int32Bits32

export
Cast Int64 Bits32 where
  cast = prim__cast_Int64Bits32

export
Cast Integer Bits32 where
  cast = prim__cast_IntegerBits32

export
Cast Bits8 Bits32 where
  cast = prim__cast_Bits8Bits32

export
Cast Bits16 Bits32 where
  cast = prim__cast_Bits16Bits32

export
Cast Bits64 Bits32 where
  cast = prim__cast_Bits64Bits32

-- To Bits64

export
Cast Int Bits64 where
  cast = prim__cast_IntBits64

export
Cast Int8 Bits64 where
  cast = prim__cast_Int8Bits64

export
Cast Int16 Bits64 where
  cast = prim__cast_Int16Bits64

export
Cast Int32 Bits64 where
  cast = prim__cast_Int32Bits64

export
Cast Int64 Bits64 where
  cast = prim__cast_Int64Bits64

export
Cast Integer Bits64 where
  cast = prim__cast_IntegerBits64

export
Cast Bits8 Bits64 where
  cast = prim__cast_Bits8Bits64

export
Cast Bits16 Bits64 where
  cast = prim__cast_Bits16Bits64

export
Cast Bits32 Bits64 where
  cast = prim__cast_Bits32Bits64
