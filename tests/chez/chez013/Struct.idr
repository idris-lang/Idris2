import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libstruct"

Point : Type
Point = Struct "point" [("x", Int), ("y", Int)]

NamedPoint : Type
NamedPoint = Struct "namedpoint" [("name", Ptr String), ("pt", Ptr Point)]

%foreign (pfn "getString")
getStr : Ptr String -> String

%foreign (pfn "mkPoint")
mkPoint : Int -> Int -> Ptr Point

%foreign (pfn "freePoint")
freePoint : Ptr Point -> PrimIO ()

%foreign (pfn "mkNamedPoint")
mkNamedPoint : String -> Ptr Point -> PrimIO (Ptr NamedPoint)

%foreign (pfn "freeNamedPoint")
freeNamedPoint : Ptr NamedPoint -> PrimIO ()

showPoint : Ptr Point -> String
showPoint pt
    = let x : Int = getField pt "x"
          y : Int = getField pt "y" in
          show (x, y)

showNamedPoint : Ptr NamedPoint -> String
showNamedPoint pt
    = let x : String = getStr (getField pt "name")
          p : Ptr Point = getField pt "pt" in
          show x ++ ": " ++ showPoint p

main : IO ()
main = do let pt = mkPoint 20 30
          np <- primIO $ mkNamedPoint "Here" pt
          setField pt "x" (the Int 40)
          putStrLn $ showPoint pt
          putStrLn $ showNamedPoint np

          primIO $ freeNamedPoint np
          primIO $ freePoint pt
