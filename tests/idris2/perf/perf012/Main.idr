%logging "compiler.identity" 5

-- This SHOULD give us the identity flag
id : Nat -> Nat
id Z = Z
id (S n) = S (id n)

-- This should NOT give us anything: `main` is not the identity
-- because it is effectful
main : IO ()
main = do
  s <- getLine
  putStrLn s
  main
