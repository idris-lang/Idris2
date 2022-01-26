{-

Test that some library functions don't cause "Maximum call stack size exceeded"
errors.

So far, only Prelude.List.++ is tested.

-}

module Main

-- Until replicate is tail recursive, we roll our own for this test.

replicateOnto : List a -> Nat -> a -> List a
replicateOnto acc Z x = acc
replicateOnto acc (S n) x = replicateOnto (x :: acc) n x

tailRecReplicate : Nat -> a -> List a
tailRecReplicate = replicateOnto []

main : IO ()
main = putStrLn $ show $ length $ tailRecReplicate 50000 () ++ [()]
