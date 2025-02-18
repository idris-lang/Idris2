module Main

import System.Concurrency

main : IO ()
main = do
    i <- getThreadId
    putStrLn $ "Current thread id: " ++ (show i)
