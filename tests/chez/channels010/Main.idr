import Data.Maybe
import System
import System.Clock
import System.Concurrency

-- `channelGetWithTimeout` on an empty channel must give up after roughly the
-- requested time: never before it, and not several times later.
main : IO ()
main = do
  c  <- the (IO (Channel Nat)) makeChannel
  t0 <- clockTime Monotonic
  r  <- channelGetWithTimeout c 500
  t1 <- clockTime Monotonic
  let d  = timeDifference t1 t0
      ms = seconds d * 1000 + nanoseconds d `div` 1000000
  putStrLn $ "timed out: " ++ show (isNothing r)
  putStrLn $ "waited at least 500 ms: " ++ show (ms >= 500)
  putStrLn $ "waited less than 2000 ms: " ++ show (ms < 2000)
