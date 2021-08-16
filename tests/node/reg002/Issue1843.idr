test : () -> IO ()
test () = putStrLn "a test"
test _  = putStrLn "oopsie"

main : IO ()
main = do test ()
          putStrLn "foo" >>= test
