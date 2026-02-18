-- Idris2

import System
import System.Concurrency

-- Test `conditionBroadcast` wakes the child with 1 main and 1 child thread

main : IO ()
main =
  do cvMutex <- makeMutex
     cv <- makeCondition
     t <- fork $ do mutexAcquire cvMutex
                    conditionWait cv cvMutex
                    putStrLn "Hello mother"
     putStrLn "Hello child"
     sleep 1
     conditionBroadcast cv
     threadWait t
