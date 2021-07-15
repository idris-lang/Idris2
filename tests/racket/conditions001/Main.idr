module Main

import Debug.Trace
import System
import System.Concurrency

-- Signal from child

main : IO ()
main = do
    mutex <- makeMutex
    cond <- makeCondition

    threadID <- fork $ do
        putStrLn "Hello"
        sleep 1
        conditionSignal cond

    mutexAcquire mutex
    conditionWait cond mutex
    putStrLn "Goodbye"
    mutexRelease mutex

    threadWait threadID
