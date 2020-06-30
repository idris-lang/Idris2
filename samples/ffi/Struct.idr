import System.FFI

libsmall : String -> String
libsmall fn = "C:" ++ fn ++ ",libsmall"

Point : Type
Point = Struct "point" [("x", Int), ("y", Int)]

%foreign (libsmall "mkPoint")
mkPoint : Int -> Int -> Point

%foreign (libsmall "freePoint")
prim_freePoint : Point -> PrimIO ()

freePoint : Point -> IO ()
freePoint p = primIO $ prim_freePoint p

showPoint : Point -> String
showPoint pt
    = let x : Int = getField pt "x"
          y : Int = getField pt "y" in
          show (x, y)

main : IO ()
main
    = do let pt = mkPoint 20 30
         setField pt "x" (the Int 40)
         putStrLn $ showPoint pt
         freePoint pt
