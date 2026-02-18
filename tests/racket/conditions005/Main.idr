-- Idris2

import System
import System.Concurrency

-- Test `conditionBroadcast` wakes all threads for 1 main and N child threads

main : IO ()
main =
  let n = 3 in
  do cvMutex <- makeMutex
     cv <- makeCondition
     ts <- for [1..n] $ \_ => fork $ do mutexAcquire cvMutex
                                        conditionWait cv cvMutex
                                        putStrLn "Hello mother"
                                        mutexRelease cvMutex
     putStrLn "Hello children"
     sleep 1
     conditionBroadcast cv
     ignore $ for ts $ \t => threadWait t
     sleep 1
