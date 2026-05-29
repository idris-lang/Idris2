import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libunion"

IntOrDouble : Type
IntOrDouble = Union "intOrDouble" [("x", Int), ("y", Double)]

%foreign (pfn "mkInt")
mkInt : Int -> IntOrDouble

%foreign (pfn "mkDouble")
mkDouble : Double -> IntOrDouble

%foreign (pfn "freeIntOrDouble")
freeIntOrDouble : IntOrDouble -> PrimIO ()

showInt : IntOrDouble -> String
showInt u =
  let x : Int = getUnionField u "x"
   in show x

showDouble : IntOrDouble -> String
showDouble u =
  let y : Double = getUnionField u "y"
   in show y

main : IO ()
main = do
  let
    u1 = mkInt 20
    u2 = mkInt 20
    u3 = mkDouble 2.1
  setUnionField u1 "x" (the Int 40)
  setUnionField u2 "y" (the Double 3.14)
  putStrLn $ showInt u1
  putStrLn $ showDouble u2
  putStrLn $ showDouble u3

  primIO $ freeIntOrDouble u1
  primIO $ freeIntOrDouble u2
  primIO $ freeIntOrDouble u3
