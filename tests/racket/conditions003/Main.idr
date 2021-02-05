module Main

import Debug.Trace
import System
import System.Concurrency

main : IO ()
main = do
    mutex <- makeMutex
    cond <- makeCondition

    thread1 <- fork $ do
        mutexAcquire mutex
        conditionWait cond mutex
        putStrLn "Goodbye"
        mutexRelease mutex

    thread2 <- fork $ do
        mutexAcquire mutex
        conditionWait cond mutex
        putStrLn "Goodbye"
        mutexRelease mutex

    putStrLn "Hello"
    conditionBroadcast cond

    threadWait thread1
    threadWait thread2
