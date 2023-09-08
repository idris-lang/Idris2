ex : {n : Nat} -> String
ex {n} = "hello" ++ show n

main : IO ()
main = putStrLn ex
