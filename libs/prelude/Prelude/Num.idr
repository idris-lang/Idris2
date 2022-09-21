module Prelude.Num

import Prelude.Basics
import Prelude.EqOrd

%default total

------------------------
-- NUMERIC INTERFACES --
------------------------

%integerLit fromInteger

||| The Num interface defines basic numerical arithmetic.
public export
interface Num ty where
  constructor MkNum
  (+) : ty -> ty -> ty
  (*) : ty -> ty -> ty
  ||| Conversion from Integer.
  fromInteger : Integer -> ty

%allow_overloads fromInteger

||| The `Neg` interface defines operations on numbers which can be negative.
public export
interface Num ty => Neg ty where
  constructor MkNeg
  ||| The underlying of unary minus. `-5` desugars to `negate (fromInteger 5)`.
  negate : ty -> ty
  (-) : ty -> ty -> ty

||| A convenience alias for `(-)`, this function enables partial application of subtraction on the
||| right-hand operand as
||| ```idris example
||| (`subtract` 1)
||| ```
||| This contrasts with `(- 1)`, which is parsed as `-1`.
export
subtract : Neg ty => ty -> ty -> ty
subtract = (-)

||| Numbers for which the absolute value is defined should implement `Abs`.
public export
interface Num ty => Abs ty where
  constructor MkAbs
  ||| Absolute value.
  abs : ty -> ty

public export
interface Num ty => Fractional ty where
  constructor MkFractional
  partial
  (/) : ty -> ty -> ty
  partial
  recip : ty -> ty

  recip x = 1 / x

public export
interface Num ty => Integral ty where
  constructor MkIntegral
  partial
  div : ty -> ty -> ty
  partial
  mod : ty -> ty -> ty

----- Instances for primitives

-- Integer

%inline
public export
Num Integer where
  (+) = prim__add_Integer
  (*) = prim__mul_Integer
  fromInteger = id

%inline
public export
Neg Integer where
  negate x = prim__sub_Integer 0 x
  (-) = prim__sub_Integer

public export
Abs Integer where
  abs x = if x < 0 then -x else x

public export
Integral Integer where
  div x y
      = case y == 0 of
             False => prim__div_Integer x y
  mod x y
      = case y == 0 of
             False => prim__mod_Integer x y

-- This allows us to pick integer as a default at the end of elaboration if
-- all other possibilities fail. I don't plan to provide a nicer syntax for
-- this...
%defaulthint
%inline
public export
defaultInteger : Num Integer
defaultInteger = %search

-- Int

%inline
public export
Num Int where
  (+) = prim__add_Int
  (*) = prim__mul_Int
  fromInteger = prim__cast_IntegerInt

%inline
public export
Neg Int where
  negate x = prim__sub_Int 0 x
  (-) = prim__sub_Int

public export
Abs Int where
  abs x = if x < 0 then -x else x

public export
Integral Int where
  div x y
      = case y == 0 of
             False => prim__div_Int x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int x y

-- Int8

%inline
public export
Num Int8 where
  (+) = prim__add_Int8
  (*) = prim__mul_Int8
  fromInteger = prim__cast_IntegerInt8

%inline
public export
Neg Int8 where
  negate x = prim__sub_Int8 0 x
  (-) = prim__sub_Int8

public export
Abs Int8 where
  abs x = if x < 0 then -x else x

public export
Integral Int8 where
  div x y
      = case y == 0 of
             False => prim__div_Int8 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int8 x y

-- Int16

%inline
public export
Num Int16 where
  (+) = prim__add_Int16
  (*) = prim__mul_Int16
  fromInteger = prim__cast_IntegerInt16

%inline
public export
Neg Int16 where
  negate x = prim__sub_Int16 0 x
  (-) = prim__sub_Int16

public export
Abs Int16 where
  abs x = if x < 0 then -x else x

public export
Integral Int16 where
  div x y
      = case y == 0 of
             False => prim__div_Int16 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int16 x y

-- Int32

%inline
public export
Num Int32 where
  (+) = prim__add_Int32
  (*) = prim__mul_Int32
  fromInteger = prim__cast_IntegerInt32

%inline
public export
Neg Int32 where
  negate x = prim__sub_Int32 0 x
  (-) = prim__sub_Int32

public export
Abs Int32 where
  abs x = if x < 0 then -x else x

public export
Integral Int32 where
  div x y
      = case y == 0 of
             False => prim__div_Int32 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int32 x y

-- Int64

%inline
public export
Num Int64 where
  (+) = prim__add_Int64
  (*) = prim__mul_Int64
  fromInteger = prim__cast_IntegerInt64

%inline
public export
Neg Int64 where
  negate x = prim__sub_Int64 0 x
  (-) = prim__sub_Int64

public export
Abs Int64 where
  abs x = if x < 0 then -x else x

public export
Integral Int64 where
  div x y
      = case y == 0 of
             False => prim__div_Int64 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int64 x y

-- Bits8

%inline
public export
Num Bits8 where
  (+) = prim__add_Bits8
  (*) = prim__mul_Bits8
  fromInteger = prim__cast_IntegerBits8

%inline
public export
Neg Bits8 where
  negate x = prim__sub_Bits8 0 x
  (-) = prim__sub_Bits8

public export
Abs Bits8 where
  abs x = if x < 0 then -x else x

public export
Integral Bits8 where
  div x y
      = case y == 0 of
             False => prim__div_Bits8 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits8 x y

-- Bits16

%inline
public export
Num Bits16 where
  (+) = prim__add_Bits16
  (*) = prim__mul_Bits16
  fromInteger = prim__cast_IntegerBits16

%inline
public export
Neg Bits16 where
  negate x = prim__sub_Bits16 0 x
  (-) = prim__sub_Bits16

public export
Abs Bits16 where
  abs x = if x < 0 then -x else x

public export
Integral Bits16 where
  div x y
      = case y == 0 of
             False => prim__div_Bits16 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits16 x y

-- Bits32

%inline
public export
Num Bits32 where
  (+) = prim__add_Bits32
  (*) = prim__mul_Bits32
  fromInteger = prim__cast_IntegerBits32

%inline
public export
Neg Bits32 where
  negate x = prim__sub_Bits32 0 x
  (-) = prim__sub_Bits32

public export
Abs Bits32 where
  abs x = if x < 0 then -x else x

public export
Integral Bits32 where
  div x y
      = case y == 0 of
             False => prim__div_Bits32 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits32 x y

-- Bits64

%inline
public export
Num Bits64 where
  (+) = prim__add_Bits64
  (*) = prim__mul_Bits64
  fromInteger = prim__cast_IntegerBits64

%inline
public export
Neg Bits64 where
  negate x = prim__sub_Bits64 0 x
  (-) = prim__sub_Bits64

public export
Abs Bits64 where
  abs x = if x < 0 then -x else x

public export
Integral Bits64 where
  div x y
      = case y == 0 of
             False => prim__div_Bits64 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits64 x y

-- Double

public export
Num Double where
  (+) = prim__add_Double
  (*) = prim__mul_Double
  fromInteger = prim__cast_IntegerDouble

%inline
public export
Neg Double where
  negate x = prim__negate_Double x
  (-) = prim__sub_Double

public export
Abs Double where
  abs x = if x < 0 then -x else x

public export
Fractional Double where
  (/) = prim__div_Double
