module IntNum

import IntEqOrd

-- This file to be deleted once these interfaces are added to prelude

-- Int8

%inline
public export
Num Int8 where
  (+) = prim__add_Int8
  (*) = prim__mul_Int8
  fromInteger = prim__cast_IntegerInt8

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

public export
Neg Bits8 where
  negate x = prim__sub_Bits8 0 x
  (-) = prim__sub_Bits8

public export
Abs Bits8 where
  abs = id

public export
Integral Bits8 where
  div x y
      = case y == 0 of
             False => prim__div_Bits8 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits8 x y

-- Bits16

public export
Neg Bits16 where
  negate x = prim__sub_Bits16 0 x
  (-) = prim__sub_Bits16

public export
Abs Bits16 where
  abs = id

public export
Integral Bits16 where
  div x y
      = case y == 0 of
             False => prim__div_Bits16 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits16 x y

-- Bits32

public export
Neg Bits32 where
  negate x = prim__sub_Bits32 0 x
  (-) = prim__sub_Bits32

public export
Abs Bits32 where
  abs = id

public export
Integral Bits32 where
  div x y
      = case y == 0 of
             False => prim__div_Bits32 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits32 x y

-- Bits64

public export
Neg Bits64 where
  negate x = prim__sub_Bits64 0 x
  (-) = prim__sub_Bits64

public export
Abs Bits64 where
  abs = id

public export
Integral Bits64 where
  div x y
      = case y == 0 of
             False => prim__div_Bits64 x y
  mod x y
      = case y == 0 of
             False => prim__mod_Bits64 x y
