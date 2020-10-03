module Main

fact : Nat -> Nat
fact 0 = 1
fact (S k) = (S k) * (fact k)

main : IO ()
main = putStrLn $ show $ fact 1000
