-- Idris2

import System
import System.Concurrency

||| Test releasing without acquiring errors correctly
main : IO ()
main =
  do m <- makeMutex
     mutexRelease m
     putStrLn "Released w/o acquiring (SHOULDN'T HAPPEN)"
