import Data.List

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
       [(0,7,0),(1,1,2),(1,3,8),(1,7,-128),(-1,7,-128)]
  ++ testOp Int8 "shr" prim__shr_Int8
       [(0,7,0),(1,1,0),(-128,1,-64),(127,3,15),(-1,3,-1)]
  ++ testOp Int8 "and" prim__and_Int8
       [(127,0,0),(-128,0,0),(23,-1,23),(-128,-1,-128),(15,8,8)]
  ++ testOp Int8 "or" prim__or_Int8
       [(127,0,127),(-128,-1,-1),(23,-1,-1),(15,64,79)]
  ++ testOp Int8 "xor" prim__xor_Int8
       [(127,0,127),(-128,-1,127),(127,-1,-128),(15,64,79),(15,1,14)]

  ++ testOp Bits8 "shl" prim__shl_Bits8
       [(0,7,0),(1,1,2),(1,3,8),(1,7,128),(255,7,128)]
  ++ testOp Bits8 "shr" prim__shr_Bits8
       [(0,7,0),(1,1,0),(255,1,127),(127,3,15),(255,3,31)]
  ++ testOp Bits8 "and" prim__and_Bits8
       [(127,0,0),(255,0,0),(23,255,23),(128,255,128),(15,8,8)]
  ++ testOp Bits8 "or" prim__or_Bits8
       [(127,0,127),(128,255,255),(23,255,255),(15,64,79)]
  ++ testOp Bits8 "xor" prim__xor_Bits8
       [(127,0,127),(128,255,127),(127,255,128),(15,64,79),(15,1,14)]

  ++ testOp Int16 "shl" prim__shl_Int16
       [(0,15,0),(1,1,2),(1,4,16),(1,15,-0x8000),(-1,15,-0x8000)]
  ++ testOp Int16 "shr" prim__shr_Int16
       [(0,15,0),(1,1,0),(-0x8000,1,-0x4000),(0x7fff,3,0x0fff),(-1,3,-1)]
  ++ testOp Int16 "and" prim__and_Int16
       [(0x7fff,0,0),(-0x8000,0,0),(23,-1,23),(-0x8000,-1,-0x8000),(15,8,8)]
  ++ testOp Int16 "or" prim__or_Int16
       [(127,0,127),(-0x8000,-1,-1),(23,-1,-1),(15,64,79)]
  ++ testOp Int16 "xor" prim__xor_Int16
       [(127,0,127),(-0x8000,-1,0x7fff),(0x7fff,-1,-0x8000),(15,64,79),(15,1,14)]

  ++ testOp Bits16 "shl" prim__shl_Bits16
       [(0,15,0),(1,1,2),(1,4,16),(1,15,0x8000),(0xffff,15,0x8000)]
  ++ testOp Bits16 "shr" prim__shr_Bits16
       [(0,15,0),(1,1,0),(0xffff,1,0x7fff),(0x7fff,3,0x0fff),(0xffff,3,0x1fff)]
  ++ testOp Bits16 "and" prim__and_Bits16
       [(0x7fff,0,0),(0xffff,0,0),(23,0xffff,23),(0x8000,0xffff,0x8000),(15,8,8)]
  ++ testOp Bits16 "or" prim__or_Bits16
       [(0x7fff,0,0x7fff),(0x8000,0xffff,0xffff),(23,0xffff,0xffff),(15,64,79)]
  ++ testOp Bits16 "xor" prim__xor_Bits16
       [(0x7fff,0,0x7fff),(0x8000,0xffff,0x7fff),(0x7fff,0xffff,0x8000),(15,64,79),(15,1,14)]

  ++ testOp Int32 "shl" prim__shl_Int32
       [(0,31,0),(1,1,2),(1,4,16),(1,31,-0x80000000),(-1,31,-0x80000000)]
  ++ testOp Int32 "shr" prim__shr_Int32
       [(0,31,0),(1,1,0),(-0x80000000,1,-0x40000000),(0x7fffffff,3,0x0fffffff),(-1,3,-1)]
  ++ testOp Int32 "and" prim__and_Int32
       [(0x7fffffff,0,0),(-0x80000000,0,0),(23,-1,23),(-0x80000000,-1,-0x80000000),(31,8,8)]
  ++ testOp Int32 "or" prim__or_Int32
       [(127,0,127),(-0x80000000,-1,-1),(23,-1,-1),(31,64,95)]
  ++ testOp Int32 "xor" prim__xor_Int32
       [(127,0,127),(-0x80000000,-1,0x7fffffff),(0x7fffffff,-1,-0x80000000),(15,64,79),(15,1,14)]

  ++ testOp Bits32 "shl" prim__shl_Bits32
       [(0,31,0),(1,1,2),(1,4,16),(1,31,0x80000000),(0xffffffff,31,0x80000000)]
  ++ testOp Bits32 "shr" prim__shr_Bits32
       [(0,31,0),(1,1,0),(0xffffffff,1,0x7fffffff),(0x7fffffff,3,0x0fffffff),(0xffffffff,3,0x1fffffff)]
  ++ testOp Bits32 "and" prim__and_Bits32
       [(0x7fffffff,0,0),(0xffffffff,0,0),(23,0xffffffff,23),(0x80000000,0xffffffff,0x80000000),(15,8,8)]
  ++ testOp Bits32 "or" prim__or_Bits32
       [(0x7fffffff,0,0x7fffffff),(0x80000000,0xffffffff,0xffffffff),(23,0xffffffff,0xffffffff),(15,64,79)]
  ++ testOp Bits32 "xor" prim__xor_Bits32
       [(0x7fffffff,0,0x7fffffff),(0x80000000,0xffffffff,0x7fffffff),(0x7fffffff,0xffffffff,0x80000000),(15,64,79),(15,1,14)]

  ++ testOp Int64 "shl" prim__shl_Int64
       [(0,63,0),(1,1,2),(1,4,16),(1,63,-0x8000000000000000),(-1,63,-0x8000000000000000)]
  ++ testOp Int64 "shr" prim__shr_Int64
       [(0,63,0),(1,1,0),(-0x8000000000000000,1,-0x4000000000000000),(0x7fffffffffffffff,3,0x0fffffffffffffff),(-1,3,-1)]
  ++ testOp Int64 "and" prim__and_Int64
       [(0x7fffffffffffffff,0,0),(-0x8000000000000000,0,0),(23,-1,23),(-0x8000000000000000,-1,-0x8000000000000000),(63,8,8)]
  ++ testOp Int64 "or" prim__or_Int64
       [(127,0,127),(-0x8000000000000000,-1,-1),(23,-1,-1),(63,64,127)]
  ++ testOp Int64 "xor" prim__xor_Int64
       [(127,0,127),(-0x8000000000000000,-1,0x7fffffffffffffff),(0x7fffffffffffffff,-1,-0x8000000000000000),(15,64,79),(15,1,14)]

  ++ testOp Bits64 "shl" prim__shl_Bits64
       [(0,63,0),(1,1,2),(1,4,16),(1,63,0x8000000000000000),(0xffffffffffffffff,63,0x8000000000000000)]
  ++ testOp Bits64 "shr" prim__shr_Bits64
       [(0,63,0),(1,1,0),(0xffffffffffffffff,1,0x7fffffffffffffff),(0x7fffffffffffffff,3,0x0fffffffffffffff),(0xffffffffffffffff,3,0x1fffffffffffffff)]
  ++ testOp Bits64 "and" prim__and_Bits64
       [(0x7fffffffffffffff,0,0),(0xffffffffffffffff,0,0),(23,0xffffffffffffffff,23),(0x8000000000000000,0xffffffffffffffff,0x8000000000000000),(15,8,8)]
  ++ testOp Bits64 "or" prim__or_Bits64
       [(0x7fffffffffffffff,0,0x7fffffffffffffff),(0x8000000000000000,0xffffffffffffffff,0xffffffffffffffff),(23,0xffffffffffffffff,0xffffffffffffffff),(15,64,79)]
  ++ testOp Bits64 "xor" prim__xor_Bits64
       [(0x7fffffffffffffff,0,0x7fffffffffffffff),(0x8000000000000000,0xffffffffffffffff,0x7fffffffffffffff),(0x7fffffffffffffff,0xffffffffffffffff,0x8000000000000000),(15,64,79),(15,1,14)]

main : IO ()
main = traverse_ putStrLn results
