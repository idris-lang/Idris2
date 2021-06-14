module IntEqOrd

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
Ord Int8 where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Int8 x y)
  (<=) x y = intToBool (prim__lte_Int8 x y)
  (>) x y = intToBool (prim__gt_Int8 x y)
  (>=) x y = intToBool (prim__gte_Int8 x y)

public export
Ord Int16 where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Int16 x y)
  (<=) x y = intToBool (prim__lte_Int16 x y)
  (>) x y = intToBool (prim__gt_Int16 x y)
  (>=) x y = intToBool (prim__gte_Int16 x y)

public export
Ord Int32 where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Int32 x y)
  (<=) x y = intToBool (prim__lte_Int32 x y)
  (>) x y = intToBool (prim__gt_Int32 x y)
  (>=) x y = intToBool (prim__gte_Int32 x y)

public export
Ord Int64 where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Int64 x y)
  (<=) x y = intToBool (prim__lte_Int64 x y)
  (>) x y = intToBool (prim__gt_Int64 x y)
  (>=) x y = intToBool (prim__gte_Int64 x y)
