-- Idris2

import System.Concurrency

||| Test basic lock/acquire and unlock/release functionality
main : IO ()
main =
  do m <- makeMutex
     mutexAcquire m
     putStrLn "Mutex acquired"
     mutexRelease m
     putStrLn "Mutex released"
