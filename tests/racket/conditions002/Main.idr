-- Idris2

import System
import System.Concurrency

-- Test `conditionSignal` works for 1 main and 1 child thread

main : IO ()
main =
  do cvMutex <- makeMutex
     cv <- makeCondition
     t <- fork $ do mutexAcquire cvMutex
                    conditionWait cv cvMutex
                    putStrLn "Hello mother"
                    mutexRelease cvMutex
     putStrLn "Hello child"
     sleep 1
     conditionSignal cv
     threadWait t
