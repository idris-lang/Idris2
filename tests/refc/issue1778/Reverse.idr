reverse : Nat -> Nat
reverse = reverseOnto 0
    where
      reverseOnto : Nat -> Nat -> Nat
      reverseOnto j 0 = j
      reverseOnto j (S k) = reverseOnto (S j) k

main : IO ()
main = printLn $ reverse $ the Nat 100000
