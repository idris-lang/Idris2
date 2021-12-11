module Issue1191

main : IO ()
main = printLn (the Nat (1 + 2))
