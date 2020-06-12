myS : Nat -> Nat
myS n = S n

myS_crash : Nat -> Nat
myS_crash = S

main : IO ()
main = do
  printLn (S Z)
  printLn (myS Z)
  printLn (myS_crash Z)
