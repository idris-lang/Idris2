import Data.List.Lazy
import Data.Stream

import Debug.Trace

S' : (pref : String) -> Nat -> Nat
S' pref = S . traceValBy (\n => "\{pref} \{show n}")

-- We return lazy values in a monad to avoid behaviour of common expression elimination

natsS' : IO $ Stream Nat
natsS' = pure $ iterate (S' "> s") Z

natsL' : IO $ LazyList Nat
natsL' = pure $ iterateN 200 (S' "> ll") Z

main : IO ()
main = do
  natsS <- natsS'

  putStrLn "\n-----------------------"
  putStrLn "first take of stream (should be `s 0..9`)"
  printLn $ take 10 natsS

  putStrLn "\n-----------------------"
  putStrLn "second take of stream (should be `s 0..9`)"
  printLn $ take 10 natsS

  natsL <- natsL'

  putStrLn "\n-----------------------"
  putStrLn "first take of short lazy list (should be `ll 0..9`)"
  printLn $ take 10 natsL

  putStrLn "\n-----------------------"
  putStrLn "second take of short lazy list (should be no `ll *`)"
  printLn $ take 10 natsL

  putStrLn "\n-----------------------"
  putStrLn "first take of longer lazy list (should be `ll 10..14`)"
  printLn $ take 15 natsL

  putStrLn "\n-----------------------"
  putStrLn "second take of longer lazy list (should be no `ll *`)"
  printLn $ take 15 natsL
