module Main

import Debug.Trace
import System
import System.Concurrency

main : IO ()
main = do
    mutex <- makeMutex
    cond <- makeCondition

    threadID <- fork $ do
        sleep 1
        putStrLn "Hello"
        conditionBroadcast cond

    mutexAcquire mutex
    conditionWait cond mutex
    putStrLn "Goodbye"
    mutexRelease mutex

    threadWait threadID
