module Main

import System

main : IO ()
main = do
    ok <- setEnv "HELLO" "HI" True
    printLn ok
    Just str <- getEnv "HELLO"
        | Nothing => pure ()
    putStrLn str
    ok <- unsetEnv "HELLO"
    printLn ok
    Just str <- getEnv "HELLO"
        | Nothing => putStrLn "Nothing there"
    pure ()
