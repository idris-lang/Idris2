module Prelude.EqOrd

import Builtin
import Prelude.Basics

%default total

------------------------
-- EQUALITY, ORDERING --
------------------------

||| The Eq interface defines inequality and equality.
||| A minimal definition includes either `(==)` or `(/=)`.
public export
interface Eq ty where
  constructor MkEq
  total
  (==) : ty -> ty -> Bool
  total
  (/=) : ty -> ty -> Bool

  x == y = not (x /= y)
  x /= y = not (x == y)

public export
Eq Void where
  _ == _ impossible

public export
Eq () where
  _ == _ = True

public export
Eq Bool where
  True == True = True
  False == False = True
  _ == _ = False

public export
Eq Int where
  x == y = intToBool (prim__eq_Int x y)

public export
Eq Integer where
  x == y = intToBool (prim__eq_Integer x y)

public export
Eq Bits8 where
  x == y = intToBool (prim__eq_Bits8 x y)

public export
Eq Bits16 where
  x == y = intToBool (prim__eq_Bits16 x y)

public export
Eq Bits32 where
  x == y = intToBool (prim__eq_Bits32 x y)

public export
Eq Bits64 where
  x == y = intToBool (prim__eq_Bits64 x y)

public export
Eq Int8 where
  x == y = intToBool (prim__eq_Int8 x y)

public export
Eq Int16 where
  x == y = intToBool (prim__eq_Int16 x y)

public export
Eq Int32 where
  x == y = intToBool (prim__eq_Int32 x y)

public export
Eq Int64 where
  x == y = intToBool (prim__eq_Int64 x y)

public export
Eq Double where
  x == y = intToBool (prim__eq_Double x y)

public export
Eq Char where
  x == y = intToBool (prim__eq_Char x y)

public export
Eq String where
  x == y = intToBool (prim__eq_String x y)

public export
Eq a => Eq b => Eq (a, b) where
  (x1, y1) == (x2, y2) = x1 == x2 && y1 == y2

public export
data Ordering = LT | EQ | GT

public export
contra : Ordering -> Ordering
contra LT = GT
contra EQ = EQ
contra GT = LT

public export
Eq Ordering where
  LT == LT = True
  EQ == EQ = True
  GT == GT = True
  _  == _  = False

||| The Ord interface defines comparison operations on ordered data types.
||| A minimal definition includes either `compare` or `(<)`.
public export
interface Eq ty => Ord ty where
  constructor MkOrd
  total
  compare : ty -> ty -> Ordering
  compare x y = if x < y then LT else if x == y then EQ else GT

  total
  (<) : ty -> ty -> Bool
  (<) x y = compare x y == LT

  total
  (>) : ty -> ty -> Bool
  (>) x y = compare x y == GT

  total
  (<=) : ty -> ty -> Bool
  (<=) x y = compare x y /= GT

  total
  (>=) : ty -> ty -> Bool
  (>=) x y = compare x y /= LT

  total
  max : ty -> ty -> ty
  max x y = if x > y then x else y

  total
  min : ty -> ty -> ty
  min x y = if (x < y) then x else y

export
comparing : Ord a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)

public export
[Reverse] (fwd : Ord a) => Ord a where
  compare x y = contra $ compare @{fwd} x y

public export
Ord Void where
  compare _ _ impossible

public export
Ord () where
  compare _ _ = EQ

public export
Ord Bool where
  compare False False = EQ
  compare False True = LT
  compare True False = GT
  compare True True = EQ

public export
Ord Int where
  (<) x y = intToBool (prim__lt_Int x y)
  (<=) x y = intToBool (prim__lte_Int x y)
  (>) x y = intToBool (prim__gt_Int x y)
  (>=) x y = intToBool (prim__gte_Int x y)

public export
Ord Integer where
  (<) x y = intToBool (prim__lt_Integer x y)
  (<=) x y = intToBool (prim__lte_Integer x y)
  (>) x y = intToBool (prim__gt_Integer x y)
  (>=) x y = intToBool (prim__gte_Integer x y)

-- Used for the nat hack
public export
compareInteger : (x, y : Integer) -> Ordering
compareInteger = compare

public export
Ord Bits8 where
  (<) x y = intToBool (prim__lt_Bits8 x y)
  (<=) x y = intToBool (prim__lte_Bits8 x y)
  (>) x y = intToBool (prim__gt_Bits8 x y)
  (>=) x y = intToBool (prim__gte_Bits8 x y)

public export
Ord Bits16 where
  (<) x y = intToBool (prim__lt_Bits16 x y)
  (<=) x y = intToBool (prim__lte_Bits16 x y)
  (>) x y = intToBool (prim__gt_Bits16 x y)
  (>=) x y = intToBool (prim__gte_Bits16 x y)

public export
Ord Bits32 where
  (<) x y = intToBool (prim__lt_Bits32 x y)
  (<=) x y = intToBool (prim__lte_Bits32 x y)
  (>) x y = intToBool (prim__gt_Bits32 x y)
  (>=) x y = intToBool (prim__gte_Bits32 x y)

public export
Ord Bits64 where
  (<) x y = intToBool (prim__lt_Bits64 x y)
  (<=) x y = intToBool (prim__lte_Bits64 x y)
  (>) x y = intToBool (prim__gt_Bits64 x y)
  (>=) x y = intToBool (prim__gte_Bits64 x y)

public export
Ord Int8 where
  (<) x y = intToBool (prim__lt_Int8 x y)
  (<=) x y = intToBool (prim__lte_Int8 x y)
  (>) x y = intToBool (prim__gt_Int8 x y)
  (>=) x y = intToBool (prim__gte_Int8 x y)

public export
Ord Int16 where
  (<) x y = intToBool (prim__lt_Int16 x y)
  (<=) x y = intToBool (prim__lte_Int16 x y)
  (>) x y = intToBool (prim__gt_Int16 x y)
  (>=) x y = intToBool (prim__gte_Int16 x y)

public export
Ord Int32 where
  (<) x y = intToBool (prim__lt_Int32 x y)
  (<=) x y = intToBool (prim__lte_Int32 x y)
  (>) x y = intToBool (prim__gt_Int32 x y)
  (>=) x y = intToBool (prim__gte_Int32 x y)

public export
Ord Int64 where
  (<) x y = intToBool (prim__lt_Int64 x y)
  (<=) x y = intToBool (prim__lte_Int64 x y)
  (>) x y = intToBool (prim__gt_Int64 x y)
  (>=) x y = intToBool (prim__gte_Int64 x y)

public export
Ord Double where
  (<) x y = intToBool (prim__lt_Double x y)
  (<=) x y = intToBool (prim__lte_Double x y)
  (>) x y = intToBool (prim__gt_Double x y)
  (>=) x y = intToBool (prim__gte_Double x y)

public export
Ord String where
  (<) x y = intToBool (prim__lt_String x y)
  (<=) x y = intToBool (prim__lte_String x y)
  (>) x y = intToBool (prim__gt_String x y)
  (>=) x y = intToBool (prim__gte_String x y)

public export
Ord Char where
  (<) x y = intToBool (prim__lt_Char x y)
  (<=) x y = intToBool (prim__lte_Char x y)
  (>) x y = intToBool (prim__gt_Char x y)
  (>=) x y = intToBool (prim__gte_Char x y)

public export
Ord a => Ord b => Ord (a, b) where
  compare (x1, y1) (x2, y2)
      = if x1 /= x2 then compare x1 x2
                    else compare y1 y2
