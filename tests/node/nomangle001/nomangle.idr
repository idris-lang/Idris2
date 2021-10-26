%foreign "javascript:lambda:(_ty,x)=>0"
prim__export : {0 a : Type} -> (x : a) -> PrimIO Int

js_export : HasIO io => a -> io ()
js_export fn = ignore $ primIO $ prim__export fn

%nomangle
foo : Int -> Int
foo x = x + 1

main : IO ()
main = do
    js_export foo
