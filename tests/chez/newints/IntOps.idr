-- Test arithmetic operations for signed integers and casts.

--------------------------------------------------------------------------------
--          Int32
--------------------------------------------------------------------------------

Num Int32 where
  (+) = prim__add_Int32
  (*) = prim__mul_Int32
  fromInteger = prim__cast_IntegerInt32

--------------------------------------------------------------------------------
--          Int64
--------------------------------------------------------------------------------

Num Int64 where
  (+) = prim__add_Int64
  (*) = prim__mul_Int64
  fromInteger = prim__cast_IntegerInt64

main : IO ()
main = pure ()
