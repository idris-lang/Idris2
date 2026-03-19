module TestThreads

-- Tests for refc_fork and refc_threadWait.
-- Note: System.Concurrency's Mutex/Condition have no C FFI bindings yet,
-- so those are not tested here.

-- Basic fork and wait.
test1 : IO ()
test1 = do
  tid <- fork $ putStrLn "hello from thread"
  threadWait tid
  putStrLn "main: thread done"

-- Two threads, sequenced via joins so output order is deterministic.
test2 : IO ()
test2 = do
  t1 <- fork $ putStrLn "thread 1"
  threadWait t1
  t2 <- fork $ putStrLn "thread 2"
  threadWait t2
  putStrLn "main: both done"

-- Fork a thread that does nothing; verify no crash.
test3 : IO ()
test3 = do
  tid <- fork $ pure ()
  threadWait tid
  putStrLn "main: silent thread done"

main : IO ()
main = do
  test1
  test2
  test3
