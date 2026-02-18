-- Idris2

import System
import System.Concurrency

-- Test `conditionSignal` wakes 1 thread for 1 main and N child threads

main : IO ()
main =
  let n = 3 in
  do cvMutex <- makeMutex
     cv <- makeCondition
     ts <- for [1..n] $ \_ => fork $ do mutexAcquire cvMutex
                                        conditionWait cv cvMutex
                                        putStrLn "Hello mother"
                                        mutexRelease cvMutex
     putStrLn "Hello child"
     sleep 1
     conditionSignal cv
     -- don't threadWait since we don't know which thread got signalled
     sleep 1
