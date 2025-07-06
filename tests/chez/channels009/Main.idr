import Data.Maybe
import System
import System.Concurrency

-- Simple producing thread.
producer : Channel Nat -> IO ()
producer c = ignore $ producer'
  where
    producer' : IO ()
    producer' = do
      channelPut c 55
      sleep 10

-- Test that channelGetWithTimeout works as expected.
main : IO ()
main =
  do c   <- makeChannel
     tid <- fork $ producer c
     val <- channelGetWithTimeout c 5
     ignore $ threadWait tid
     putStrLn $ show val

