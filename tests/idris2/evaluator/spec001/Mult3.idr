%inline %spec m
smult : (m, n : Nat) -> Nat
smult 0 n = 0
smult 1 n = n
smult (S m) n = n + smult m n

main : IO ()
main = do
  n <- getLine
  let p = cast n
  printLn (smult 3 p)
