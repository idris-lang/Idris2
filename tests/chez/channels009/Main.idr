import Data.Maybe
import System
import System.Concurrency

-- Simple producing thread.
producer : Channel Nat -> IO ()
producer c = ignore $ producer' 1000
  where
    producer' : Nat -> IO ()
    producer' Z     = pure ()
    producer' (S n) = do
      channelPut c n
      sleep 1

-- Test that channelGetWithTimeout works as expected.
main : IO ()
main =
  do c   <- makeChannel
     tid <- fork $ producer c
     val <- channelGetWithTimeout c 5
     ignore $ threadWait tid
     putStrLn $ show val

