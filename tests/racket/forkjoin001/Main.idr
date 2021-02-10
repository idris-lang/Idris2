module Main

import System

main : IO ()
main = do
    threadID <- fork $ do
        sleep 1
        putStrLn "Hello"
    threadWait threadID
    putStrLn "Goodbye"
