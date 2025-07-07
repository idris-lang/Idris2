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

-- Test that channelGetWithTimeout fails under contention.
main : IO ()
main = do
  c    <- makeChannel
  tids <- for [0..11] $ \n =>
    fork $ producer c n
  ()   <- sleep 20
  vals <- for [0..11] $ \_ =>
    fork ( do val <- channelGetWithTimeout c 1000
              putStrLn $ "Thread got: " ++ show val
         )
  ignore $ traverse (\t => threadWait t) tids
  ignore $ traverse (\t => threadWait t) vals

