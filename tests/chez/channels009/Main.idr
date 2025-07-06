import Data.Maybe
import System
import System.Concurrency

-- Simple producing thread.
producer : Channel Nat -> Nat -> IO ()
producer c n = ignore $ producer' n
  where
    producer' : Nat -> IO ()
    producer' Z     = pure ()
    producer' (S n) = do
      channelPut c n
      sleep 1

-- Test that channelGetWithTimeout works as expected.
main : IO ()
main =
  do c    <- makeChannel
     tids <- for [0..100] $ \n => fork $ producer c n
     val  <- channelGetWithTimeout c 1
     ignore $ traverse (\t => threadWait t) tids
     putStrLn $ show val

