module Main

import Debug.Trace
import System
import System.Concurrency

main : IO ()
main = do
    mutex <- makeMutex
    cond <- makeCondition

    threadID <- fork $ do
        mutexAcquire mutex
        conditionWait cond mutex
        putStrLn "Goodbye"
        mutexRelease mutex

    putStrLn "Hello"
    conditionSignal cond

    threadWait threadID
