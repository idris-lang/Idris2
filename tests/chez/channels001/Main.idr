module Main

import System
import System.Concurrency

main : IO ()
main = do
    chan <- makeChannel
    threadID <- fork $ do
        channelPut chan "Hello"
        channelPut chan "Goodbye"
    val <- channelGet chan
    putStrLn val
    val <- channelGet chan
    putStrLn val
    sleep 1
