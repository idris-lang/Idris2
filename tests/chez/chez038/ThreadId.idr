module Main

import System
import System.Concurrency

main : IO ()
main = do
    tid0  <- getThreadId
    putStrLn $ "Current thread id: " ++ (show tid0)
    i <- fork $ do
      tid1 <- getThreadId
      putStrLn $ "Forked thread id: " ++ (show tid1)
    threadWait i
