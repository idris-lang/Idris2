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

-- To Char

export
Cast Int Char where
  cast = prim__cast_IntChar

-- To Double

export
Cast Int Double where
  cast = prim__cast_IntDouble

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
