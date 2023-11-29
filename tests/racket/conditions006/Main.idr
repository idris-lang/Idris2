-- Disabled for now: no working
-- conditionWaitTimeout
-- for racket

-- Idris2

import System
import System.Concurrency

-- Test `conditionWaitTimeout` times out for 1 main and 1 child thread

main : IO ()
main =
  do cvMutex <- makeMutex
     cv <- makeCondition
     t <- fork $ do mutexAcquire cvMutex
                    conditionWaitTimeout cv cvMutex 1000000
                    putStrLn "Where are you mother?"
                    mutexRelease cvMutex
     sleep 2
     putStrLn "Sorry I'm late child!"
     threadWait t
