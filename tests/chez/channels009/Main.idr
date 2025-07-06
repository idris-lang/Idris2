import Data.Maybe
import System
import System.Concurrency

-- Simple producing thread.
producer : Channel Nat -> IO ()
producer c = ignore $ producer' 10000000
  where
    producer' : Nat -> IO ()
    producer' Z     = pure ()
    producer' (S n) = do
      channelPut c n

-- Test that channelGetWithTimeout works as expected.
main : IO ()
main =
  do c   <- makeChannel
     tid <- fork $ producer c
     val <- channelGetWithTimeout c 1
     ignore $ threadWait tid
     putStrLn $ show val

