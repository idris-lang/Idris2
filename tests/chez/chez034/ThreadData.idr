module Main

import System.Concurrency

child : Condition -> Mutex -> IO ()
child cond mtx = do
    mutexAcquire mtx
    str <- getThreadData String
    putStrLn $ "child data: " ++ (show str)

    setThreadData 17
    i <- getThreadData Int
    putStrLn $ "child data now: " ++ (show i)

    conditionSignal cond
    conditionWait cond mtx

    putStrLn $ "child exiting"

    conditionSignal cond
    mutexRelease mtx


main : IO ()
main = do
    setThreadData 13
    i <- getThreadData Int
    putStrLn $ "parent data initialized to: " ++ (show i)

    setThreadData "hello"
    str <- getThreadData String
    putStrLn $ "parent data now: " ++ (show str)

    mtx <- makeMutex
    cond <- makeCondition

    mutexAcquire mtx
    _ <- fork (child cond mtx)
    conditionWait cond mtx

    str2 <- getThreadData String
    putStrLn $ "parent data still: " ++ (show str2)

    conditionSignal cond
    conditionWait cond mtx

    putStrLn $ "parent exiting"
    mutexRelease mtx
