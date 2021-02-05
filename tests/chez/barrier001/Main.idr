module Main

import System
import System.Concurrency

main : IO ()
main = do
    barrier <- makeBarrier 3
    threadIDs <- for [1,2,3] $ \n => fork $ do
        putStrLn "Hello"
        barrierWait barrier
        putStrLn "Goodbye"
    for threadIDs $ \threadID =>
        threadWait threadID
    sleep 1
