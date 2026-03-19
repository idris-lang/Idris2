-- RefC FFI struct test.
-- Tests struct-by-pointer passing and getField/setField via the descriptor registry.
-- Uses Int32 for C's int32_t fields (Int would be 64-bit in RefC).
import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libstruct,struct.h"

Point : Type
Point = Struct "point" [("x", Int32), ("y", Int32)]

NamedPoint : Type
NamedPoint = Struct "namedpoint" [("name", Ptr String), ("pt", Point)]

%foreign (pfn "mkPoint")
mkPoint : Int32 -> Int32 -> Point

%foreign (pfn "freePoint")
freePoint : Point -> PrimIO ()

%foreign (pfn "mkNamedPoint")
mkNamedPoint : String -> Point -> PrimIO NamedPoint

%foreign (pfn "freeNamedPoint")
freeNamedPoint : NamedPoint -> PrimIO ()

showPoint : Point -> String
showPoint pt =
    let x : Int32 = getField pt "x"
        y : Int32 = getField pt "y"
    in "(" ++ show x ++ ", " ++ show y ++ ")"

main : IO ()
main = do
    let pt = mkPoint 20 30
    putStrLn $ "initial:  " ++ showPoint pt
    setField pt "x" (the Int32 40)
    putStrLn $ "after set: " ++ showPoint pt

    np <- primIO $ mkNamedPoint "Here" pt
    let name : Ptr String = getField np "name"
    let nested : Point    = getField np "pt"
    putStrLn $ "nested x: " ++ show (the Int32 (getField nested "x"))

    primIO $ freeNamedPoint np
    primIO $ freePoint pt
    putStrLn "done"
