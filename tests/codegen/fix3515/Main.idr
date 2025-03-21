toNat : Nat -> () -> Nat
toNat 0 () = 1
toNat _ _ = 0

main : IO ()
main = do
    printLn $ toNat 0 ()
    printLn $ toNat 1 ()
