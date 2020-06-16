module Main

import System

main : IO ()
main = do
    ok <- setEnv "HELLO" "HI" False
    printLn ok
    Just str <- getEnv "HELLO"
        | Nothing => pure ()
    putStrLn str
    ok <- setEnv "HELLO" "HO" False
    printLn ok
    ok <- setEnv "HELLO" "EH" True
    printLn ok
    ok <- unsetEnv "HELLO"
    printLn ok
    Just str <- getEnv "HELLO"
        | Nothing => putStrLn "Nothing there"
    pure ()
