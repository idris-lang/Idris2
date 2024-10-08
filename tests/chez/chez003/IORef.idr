import Data.IORef
import System.Concurrency

slowinc : Nat -> Nat -> Nat
slowinc 0     j = S j
slowinc (S k) j = slowinc k j

parameters (ref  : IORef Nat)
           (lock : Mutex)

  runFastInc : Nat -> IO ()
  runFastInc 0     = pure ()
  runFastInc (S k) = atomically lock (modifyIORef ref S) >> runFastInc k

  runSlowInc : Nat -> IO ()
  runSlowInc 0     = pure ()
  runSlowInc (S k) = atomically lock (modifyIORef ref (slowinc 10000)) >> runSlowInc k

main : IO ()
main
    = do x <- newIORef 42
         let y = x
         writeIORef y 94
         val <- readIORef x
         printLn val
         val <- readIORef y
         printLn val
         modifyIORef x (* 2)
         val <- readIORef x
         printLn val
         val <- readIORef y
         printLn val
         lock <- makeMutex
         ref  <- newIORef Z
         readIORef ref >>= printLn
         t1  <- fork $
           runFastInc ref lock 1_000_000
         t2  <- fork $
           runSlowInc ref lock 1_0000
         threadWait t1
         threadWait t2
         readIORef ref >>= printLn
