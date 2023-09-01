foo : Int -> IO Int
foo x = pure x

main : IO ()
main = putStrLn !(foo 10)
