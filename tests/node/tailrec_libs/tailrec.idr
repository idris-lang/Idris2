{-

Test that some library functions don't cause "Maximum call stack size exceeded"
errors.

So far, only Prelude.List.++ is tested.

-}

module Main

-- Until length and replicate are tail recursive, we roll our own for this test.

lengthPlus : Nat -> List a -> Nat
lengthPlus n [] = n
lengthPlus n (x::xs) = lengthPlus (S n) xs

tailRecLength : List a -> Nat
tailRecLength = lengthPlus Z

replicateOnto : List a -> Nat -> a -> List a
replicateOnto acc Z x = acc
replicateOnto acc (S n) x = replicateOnto (x :: acc) n x

tailRecReplicate : Nat -> a -> List a
tailRecReplicate = replicateOnto []

main : IO ()
main = putStrLn $ show $ tailRecLength $ tailRecReplicate 10000 () ++ [()]
