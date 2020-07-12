module Prelude.Num

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Ops

%default total

------------------------
-- NUMERIC INTERFACES --
------------------------

%integerLit fromInteger

||| The Num interface defines basic numerical arithmetic.
public export
interface Num ty where
  (+) : ty -> ty -> ty
  (*) : ty -> ty -> ty
  ||| Conversion from Integer.
  fromInteger : Integer -> ty

%allow_overloads fromInteger

||| The `Neg` interface defines operations on numbers which can be negative.
public export
interface Num ty => Neg ty where
  ||| The underlying of unary minus. `-5` desugars to `negate (fromInteger 5)`.
  negate : ty -> ty
  (-) : ty -> ty -> ty

||| Numbers for which the absolute value is defined should implement `Abs`.
public export
interface Num ty => Abs ty where
  ||| Absolute value.
  abs : ty -> ty

public export
interface Num ty => Fractional ty where
  partial
  (/) : ty -> ty -> ty
  partial
  recip : ty -> ty

  recip x = 1 / x

public export
interface Num ty => Integral ty where
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

-- Bits8

%inline
public export
Num Bits8 where
  (+) = prim__add_Bits8
  (*) = prim__mul_Bits8
  fromInteger = prim__cast_IntegerBits8

-- Bits16

%inline
public export
Num Bits16 where
  (+) = prim__add_Bits16
  (*) = prim__mul_Bits16
  fromInteger = prim__cast_IntegerBits16

-- Bits32

%inline
public export
Num Bits32 where
  (+) = prim__add_Bits32
  (*) = prim__mul_Bits32
  fromInteger = prim__cast_IntegerBits32

-- Bits64

%inline
public export
Num Bits64 where
  (+) = prim__add_Bits64
  (*) = prim__mul_Bits64
  fromInteger = prim__cast_IntegerBits64

-- Double

public export
Num Double where
  (+) = prim__add_Double
  (*) = prim__mul_Double
  fromInteger = prim__cast_IntegerDouble

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
