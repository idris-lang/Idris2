import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libstruct"

Point : Type
Point = Struct "point" [("x", Int), ("y", Int)]

NamedPoint : Type
NamedPoint = Struct "namedpoint" [("name", Ptr String), ("pt", Ptr Point)]

InlinedPoint : Type
InlinedPoint = Struct "inlinedpoint" [("name", Ptr String), ("pt", Point)]

%foreign (pfn "getString")
getStr : Ptr String -> String

%foreign (pfn "mkPoint")
mkPoint : Int -> Int -> Ptr Point

%foreign (pfn "freePoint")
freePoint : Ptr Point -> PrimIO ()

mkGCPoint : Int -> Int -> IO (GCPtr Point)
mkGCPoint x y =
  onCollect (mkPoint x y) (primIO . freePoint)

%foreign (pfn "mkNamedPoint")
mkNamedPoint : String -> Ptr Point -> PrimIO (Ptr NamedPoint)

%foreign (pfn "freeNamedPoint")
freeNamedPoint : Ptr NamedPoint -> PrimIO ()

%foreign (pfn "mkInlinedPoint")
mkInlinedPoint : String -> Int -> Int -> Ptr InlinedPoint

%foreign (pfn "freeInlinedPoint")
freeInlinedPoint : Ptr InlinedPoint -> PrimIO ()

showPoint : Ptr Point -> String
showPoint pt
    = let x : Int = getField pt "x"
          y : Int = getField pt "y" in
          show (x, y)

showGCPoint : GCPtr Point -> String
showGCPoint pt
    = let x : Int = getGCField pt "x"
          y : Int = getGCField pt "y" in
          show (x, y)

showNamedPoint : Ptr NamedPoint -> String
showNamedPoint pt
    = let x : String = getStr (getField pt "name")
          p : Ptr Point = getField pt "pt" in
          show x ++ ": " ++ showPoint p

showInlinedPoint : Ptr InlinedPoint -> String
showInlinedPoint pt
    = let n : String = getStr (getField pt "name")
          x : Int = getField pt "pt x"
          y : Int = getField pt "pt y" in
          show n ++ ": " ++ show (x, y)

main : IO ()
main = do let pt = mkPoint 20 30
              ip = mkInlinedPoint "There" 1 2
          np <- primIO $ mkNamedPoint "Here" pt
          gp <- mkGCPoint 13 181
          setField pt "x" (the Int 40)
          setField ip "pt x" (the Int 15)
          putStrLn $ showPoint pt
          putStrLn $ showInlinedPoint ip
          putStrLn $ showNamedPoint np
          putStrLn $ showGCPoint gp

          let ippt = getFieldPtr ip "pt"
          putStrLn $ showPoint ippt

          setField ip "pt x" (the Int 3)
          setField ip "pt y" (the Int 4)
          putStrLn $ showInlinedPoint ip

          setField np "pt * x" (the Int 5)
          let x : Int = getField np "pt * x"
          putStrLn $ show x
          putStrLn $ showNamedPoint np

          primIO $ freeNamedPoint np
          primIO $ freeInlinedPoint ip
          primIO $ freePoint pt
