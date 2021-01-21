%foreign "javascript:lambda: (x) => console.log('ok')"
prim__ok : Double -> PrimIO ()

main : HasIO io => io ()
main = do
    primIO $ prim__ok 0
    primIO $ prim__ok 99
    primIO $ prim__ok 100
    primIO $ prim__ok (-1)
    primIO $ prim__ok 1234567890
