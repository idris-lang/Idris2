-- Idris2

import System
import System.Concurrency

-- Test that acquiring the mutex in the parent, then the child blocks correctly
main : IO ()
main =
  do m <- makeMutex
     mutexAcquire m
     putStrLn "Main acquired mutex"
     t <- fork $ do mutexAcquire m
                    putStrLn "Child acquired mutex"
                    sleep 2
                    mutexRelease m
                    putStrLn "Child released mutex"
     sleep 1
     mutexRelease m
     putStrLn "Main released mutex"
     threadWait t
