module TestConcurrency

import System.Concurrency
import Data.IORef

-- Mutex: protect a shared counter incremented by two threads.
testMutex : IO ()
testMutex = do
  m   <- makeMutex
  ref <- newIORef (the Int 0)
  let bump = do
        mutexAcquire m
        n <- readIORef ref
        writeIORef ref (n + 1)
        mutexRelease m
  t1 <- fork bump
  t2 <- fork bump
  threadWait t1
  threadWait t2
  n <- readIORef ref
  putStrLn $ "mutex counter = " ++ show n

-- Condition variable: producer signals consumer.
conditionLoop : IORef Bool -> Condition -> Mutex -> IO ()
conditionLoop ref cond m = do
  ready <- readIORef ref
  if ready
    then mutexRelease m
    else do conditionWait cond m
            mutexAcquire m
            conditionLoop ref cond m

testCondition : IO ()
testCondition = do
  m    <- makeMutex
  cond <- makeCondition
  ref  <- newIORef False
  let producer = do
        mutexAcquire m
        writeIORef ref True
        conditionSignal cond
        mutexRelease m
  let consumer = do
        mutexAcquire m
        conditionLoop ref cond m
        putStrLn "consumer: got signal"
  tc <- fork consumer
  tp <- fork producer
  threadWait tp
  threadWait tc

-- Semaphore: two threads post, main waits twice.
testSemaphore : IO ()
testSemaphore = do
  s <- makeSemaphore 0
  t1 <- fork $ semaphorePost s
  t2 <- fork $ semaphorePost s
  semaphoreWait s
  semaphoreWait s
  threadWait t1
  threadWait t2
  putStrLn "semaphore: received 2 posts"

-- Barrier: three threads rendezvous.
testBarrier : IO ()
testBarrier = do
  b  <- makeBarrier 3
  ref <- newIORef (the Int 0)
  let arrive = do
        barrierWait b
        n <- readIORef ref -- all three arrived before any reads
        pure ()
  t1 <- fork arrive
  t2 <- fork arrive
  barrierWait b          -- main thread is the third participant
  writeIORef ref 42
  threadWait t1
  threadWait t2
  putStrLn "barrier: all three met"

main : IO ()
main = do
  testMutex
  testCondition
  testSemaphore
  testBarrier
