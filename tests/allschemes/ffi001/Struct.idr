import System.FFI

PtrAST : Type
PtrAST = Struct "AST" [("value", AnyPtr)]

%foreign "C:freeAST,foo"
prim_freeAST : (PtrAST -> Int) -> PrimIO ()

freeAST : HasIO io => (PtrAST -> Int) -> io ()
freeAST ast = primIO $ prim_freeAST ast

main : IO ()
main = freeAST (\x => 1)
