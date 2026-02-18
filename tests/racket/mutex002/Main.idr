-- Idris2

import System.Concurrency

||| Test basic lock/acquire and unlock/release functionality from child thread
main : IO ()
main =
  do m <- makeMutex
     t <- fork $ do mutexAcquire m
                    putStrLn "Child acquired mutex"
                    mutexRelease m
                    putStrLn "Child released mutex"
     threadWait t
