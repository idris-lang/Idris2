replicateTR : Nat -> a -> List a
replicateTR n v = go n Nil
  where go : Nat -> List a -> List a
        go 0     as = as
        go (S k) as = go k (v :: as)

main : IO ()
main =  printLn (length $ fastPack $ replicateTR 1000000 '0')
     >> putStrLn (fastConcat $ replicateTR 1000000 "")
