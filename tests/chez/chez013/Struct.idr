import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libstruct"

Point : Type
Point = Struct "point" [("x", Int), ("y", Int)]

NamedPoint : Type
NamedPoint = Struct "namedpoint" [("name", Ptr String), ("pt", Point)]

%foreign (pfn "getString")
getStr : Ptr String -> String

%foreign (pfn "mkPoint")
mkPoint : Int -> Int -> Point

%foreign (pfn "freePoint")
freePoint : Point -> PrimIO ()

%foreign (pfn "mkNamedPoint")
mkNamedPoint : String -> Point -> PrimIO NamedPoint

%foreign (pfn "freeNamedPoint")
freeNamedPoint : NamedPoint -> PrimIO ()

showPoint : Point -> String
showPoint pt
    = let x : Int = getField pt "x"
          y : Int = getField pt "y" in
          show (x, y)

showNamedPoint : NamedPoint -> String
showNamedPoint pt
    = let x : String = getStr (getField pt "name")
          p : Point = getField pt "pt" in
          show x ++ ": " ++ showPoint p

main : IO ()
main = do let pt = mkPoint 20 30
          np <- primIO $ mkNamedPoint "Here" pt
          setField pt "x" (the Int 40)
          putStrLn $ showPoint pt
          putStrLn $ showNamedPoint np

          primIO $ freeNamedPoint np
          primIO $ freePoint pt
