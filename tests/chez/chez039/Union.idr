import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libunion"

IntOrDouble : Type
IntOrDouble = Union "intOrDouble" [("x", Int), ("y", Double)]

Case0 : Type
Case0 = Struct "case0" [("tag0", Bits8), ("x", Int)]

TaggedUnion : Type
TaggedUnion = Union "taggedUnion"
  [ ("case0", Case0)
  , ("case1", Struct "case1" [("tag1", Bits8), ("y", Double), ("z", Int)])
  ]

%foreign (pfn "mkInt")
mkInt : Int -> Ptr IntOrDouble

%foreign (pfn "mkDouble")
mkDouble : Double -> Ptr IntOrDouble

%foreign (pfn "freeIntOrDouble")
freeIntOrDouble : Ptr IntOrDouble -> PrimIO ()

%foreign (pfn "mkTaggedUnion0")
mkTaggedUnion0 : Int -> Ptr TaggedUnion

%foreign (pfn "mkTaggedUnion1")
mkTaggedUnion1 : Double -> Int -> Ptr TaggedUnion

%foreign (pfn "freeTaggedUnion")
freeTaggedUnion : Ptr TaggedUnion -> PrimIO ()

showInt : Ptr IntOrDouble -> String
showInt u =
  let x : Int = getCase u "x"
   in show x

showDouble : Ptr IntOrDouble -> String
showDouble u =
  let y : Double = getCase u "y"
   in show y

showTaggedUnion : Ptr TaggedUnion -> String
showTaggedUnion u =
  let tag : Bits8 = getCase u "case0 tag0"
   in case tag of
     0 =>
       let x : Int = getCase u "case0 x"
        in "case 0, x: " ++ show x
     _ =>
       let y : Double = getCase u "case1 y"
           z : Int = getCase u "case1 z"
        in "case 1, y: " ++ show y ++ ", z: " ++ show z

main : IO ()
main = do
  let
    u0 = mkInt 20
    u1 = mkInt 20
    u2 = mkDouble 2.1

    t0 = mkTaggedUnion0 24
    t1 = mkTaggedUnion1 3.14 42

  setCase u0 "x" (the Int 40)
  setCase u1 "y" (the Double 3.14)
  putStrLn $ showInt u0
  putStrLn $ showDouble u1
  putStrLn $ showDouble u2

  putStrLn $ showTaggedUnion t0
  putStrLn $ showTaggedUnion t1
  setCase t1 "case0 tag0" (the Bits8 0)
  setCase t1 "case0 x" (the Int 41)
  putStrLn $ showTaggedUnion t1

  let c0 : Ptr Case0 = getCasePtr t1 "case0"
  setField c0 "x" (the Int 100)
  let x : Int = getField c0 "x"
  putStrLn $ "case 0 ptr, x: " ++ show x
  setCase t1 "case0 x" (the Int 99)
  let x : Int = getField c0 "x"
  putStrLn $ "case 0 ptr, x: " ++ show x

  primIO $ freeIntOrDouble u0
  primIO $ freeIntOrDouble u1
  primIO $ freeIntOrDouble u2

  primIO $ freeTaggedUnion t0
  primIO $ freeTaggedUnion t1
