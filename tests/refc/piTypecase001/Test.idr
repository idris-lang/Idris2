module Test

typeof : Type -> String
typeof (_ -> _) = "->"
typeof _ = "Other"

main : IO ()
main = do
    putStrLn $ typeof (Int -> Int)
    putStrLn $ typeof (Nat -> Int)
    putStrLn $ typeof Nat
    putStrLn $ typeof Int
