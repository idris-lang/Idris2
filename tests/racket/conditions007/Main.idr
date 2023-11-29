-- Disabled for now: no working
-- conditionWaitTimeout
-- for racket

-- Idris2

import System
import System.Concurrency

-- Test `conditionWaitTimeout` times out m of n threads for 1 main and n child
-- threads

main : IO ()
main =
  let
    n = 5
    m = 3
  in
    do cvMutex <- makeMutex
       cv <- makeCondition

       -- spawn n-m inifinitely patient children
       waiting <- for [1..(n - m)] $ \_ => fork $
             do mutexAcquire cvMutex
                conditionWait cv cvMutex
                putStrLn "Woke up despite no timeout (SHOULDN'T HAPPEN)"
                mutexRelease cvMutex

       -- spawn m impatient children
       impatients <- for [1..m] $ \_ => fork $
             do mutexAcquire cvMutex
                conditionWaitTimeout cv cvMutex 1000000
                putStrLn "Where are you mother?"
                mutexRelease cvMutex

       sleep m
       putStrLn "Sorry I'm late children! Weren't there more of you?..."
       for_ impatients $ \t => threadWait t
       sleep 1
