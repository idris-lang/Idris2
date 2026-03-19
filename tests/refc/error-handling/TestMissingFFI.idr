-- Test that calling a %foreign function with no C binding prints
-- the Idris function name and exits cleanly (not a SIGTRAP/crash).

-- Only has a scheme: binding — the RefC codegen emits a named stub.
%foreign "scheme:blodwen-make-channel"
prim__schemeOnlyFunc : PrimIO Int

main : IO ()
main = do
  putStrLn "about to call unimplemented FFI"
  _ <- primIO prim__schemeOnlyFunc
  putStrLn "should not reach here"
