-- Idris2

import System
import System.Concurrency

||| Test double-release errors correctly
main : IO ()
main =
  do m <- makeMutex
     mutexAcquire m
     putStrLn "Mutex acquired"
     mutexRelease m
     putStrLn "1st release"
     mutexRelease m
     putStrLn "2nd release (SHOULDN'T HAPPEN)"
