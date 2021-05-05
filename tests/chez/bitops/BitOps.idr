import Data.List

--------------------------------------------------------------------------------
--          Int8
--------------------------------------------------------------------------------

Show Int8 where
  show = prim__cast_Int8String

public export
Eq Int8 where
  x == y = intToBool (prim__eq_Int8 x y)

Num Int8 where
  (+) = prim__add_Int8
  (*) = prim__mul_Int8
  fromInteger = prim__cast_IntegerInt8

Neg Int8 where
  (-)    = prim__sub_Int8
  negate = prim__sub_Int8 0

--------------------------------------------------------------------------------
--          Int16
--------------------------------------------------------------------------------

Show Int16 where
  show = prim__cast_Int16String

public export
Eq Int16 where
  x == y = intToBool (prim__eq_Int16 x y)

Num Int16 where
  (+) = prim__add_Int16
  (*) = prim__mul_Int16
  fromInteger = prim__cast_IntegerInt16

Neg Int16 where
  (-)    = prim__sub_Int16
  negate = prim__sub_Int16 0

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

showTpe : Type -> String
showTpe Bits16  = "Bits16"
showTpe Bits32  = "Bits32"
showTpe Bits64  = "Bits64"
showTpe Bits8   = "Bits8"
showTpe Int     = "Int"
showTpe Int16   = "Int16"
showTpe Int32   = "Int32"
showTpe Int64   = "Int64"
showTpe Int8    = "Int8"
showTpe Integer = "Integer"
showTpe _       = "unknown type"

testOp : (a: Type) -> (Show a, Eq a)
         => (opName : String)
         -> (op : a -> a -> a)
         -> List (a,a,a)
         -> List String
testOp a n op = mapMaybe doTest
  where doTest : (a,a,a) -> Maybe String
        doTest (x,y,res) =
          let myRes = op x y
           in if myRes == res then Nothing
              else Just $  #"Invalid result for \#{n} on \#{showTpe a}. "#
                        ++ #"Inputs: \#{show x}, \#{show y}. "#
                        ++ #"Expected \#{show res} but got \#{show myRes}."#

results : List String
results =
     testOp Int8 "shl" prim__shl_Int8
       [(0,7,0),(1,1,2),(1,3,8),(1,7,-128),(1,8,0),(-1,7,-128)]
  ++ testOp Int8 "shr" prim__shr_Int8
       [(0,7,0),(1,1,0),(-128,1,-64),(127,3,15),(-128,8,-1),(-1,3,-1)]
  ++ testOp Int8 "and" prim__and_Int8
       [(127,0,0),(-128,0,0),(23,-1,23),(-128,-1,-128),(15,8,8)]
  ++ testOp Int8 "or" prim__or_Int8
       [(127,0,127),(-128,-1,-1),(23,-1,-1),(15,64,79)]
  ++ testOp Int8 "xor" prim__xor_Int8
       [(127,0,127),(-128,-1,127),(127,-1,-128),(15,64,79),(15,1,14)]

  ++ testOp Bits8 "shl" prim__shl_Bits8
       [(0,7,0),(1,1,2),(1,3,8),(1,7,128),(1,8,0),(255,7,128)]
  ++ testOp Bits8 "shr" prim__shr_Bits8
       [(0,7,0),(1,1,0),(255,1,127),(127,3,15),(255,8,0),(255,3,31)]
  ++ testOp Bits8 "and" prim__and_Bits8
       [(127,0,0),(255,0,0),(23,255,23),(128,255,128),(15,8,8)]
  ++ testOp Bits8 "or" prim__or_Bits8
       [(127,0,127),(128,255,255),(23,255,255),(15,64,79)]
  ++ testOp Bits8 "xor" prim__xor_Bits8
       [(127,0,127),(128,255,127),(127,255,128),(15,64,79),(15,1,14)]

  ++ testOp Int16 "shl" prim__shl_Int16
       [(0,15,0),(1,1,2),(1,4,16),(1,15,-0x8000),(1,16,0),(-1,15,-0x8000)]
  ++ testOp Int16 "shr" prim__shr_Int16
       [(0,15,0),(1,1,0),(-0x8000,1,-0x4000),(0x7fff,3,0x0fff),(-0x8000,16,-1),(-1,3,-1)]
  ++ testOp Int16 "and" prim__and_Int16
       [(0x7fff,0,0),(-0x8000,0,0),(23,-1,23),(-0x8000,-1,-0x8000),(15,8,8)]
  ++ testOp Int16 "or" prim__or_Int16
       [(127,0,127),(-0x8000,-1,-1),(23,-1,-1),(15,64,79)]
  ++ testOp Int16 "xor" prim__xor_Int16
       [(127,0,127),(-0x8000,-1,0x7fff),(0x7fff,-1,-0x8000),(15,64,79),(15,1,14)]

  ++ testOp Bits16 "shl" prim__shl_Bits16
       [(0,15,0),(1,1,2),(1,4,16),(1,15,0x8000),(1,16,0),(0xffff,15,0x8000)]
  ++ testOp Bits16 "shr" prim__shr_Bits16
       [(0,15,0),(1,1,0),(0xffff,1,0x7fff),(0x7fff,3,0x0fff),(0xffff,16,0),(0xffff,3,0x1fff)]
  ++ testOp Bits16 "and" prim__and_Bits16
       [(0x7fff,0,0),(0xffff,0,0),(23,0xffff,23),(0x8000,0xffff,0x8000),(15,8,8)]
  ++ testOp Bits16 "or" prim__or_Bits16
       [(0x7fff,0,0x7fff),(0x8000,0xffff,0xffff),(23,0xffff,0xffff),(15,64,79)]
  ++ testOp Bits16 "xor" prim__xor_Bits16
       [(0x7fff,0,0x7fff),(0x8000,0xffff,0x7fff),(0x7fff,0xffff,0x8000),(15,64,79),(15,1,14)]

main : IO ()
main = traverse_ putStrLn results
