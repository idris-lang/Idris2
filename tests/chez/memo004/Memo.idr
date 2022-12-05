import Data.List.Lazy

import Debug.Trace

S' : (pref : String) -> Nat -> Nat
S' pref = S . traceValBy (\n => "\{pref} \{show n}")

-- We return lazy values in a monad to avoid behaviour of common expression elimination

natsL' : IO $ LazyList Nat
natsL' = pure $ iterateN 200 (S' "> ll") Z

%foreign "scheme:collect"
prim__gc : PrimIO ()

gc : IO ()
gc = primIO prim__gc

main : IO ()
main = do
  natsL <- natsL'

  putStrLn "\n-----------------------"
  putStrLn "first take of lazy list (should be `ll 0..9`)"
  printLn $ take 10 natsL

  putStrLn "\n-----------------------"
  putStrLn "second take of lazy list (should be no `ll *`)"
  printLn $ take 10 natsL

  gc

  putStrLn "\n-----------------------"
  putStrLn "take of lazy list after gc (should be `ll 0..9`)"
  printLn $ take 10 natsL
