import Data.Maybe
import System
import System.Concurrency

-- One reader
reader : Channel Nat -> IO ()
reader c = do
  val <- channelGetWithTimeout c 8
  case val of
    Just _  =>
      putStrLn "Thread got: Just _"
    Nothing =>
      putStrLn "Thread got: Nothing"

-- One producer (delayed)
producer : Channel Nat -> Nat -> IO ()
producer c n =
  channelPut c n

main : IO ()
main = do
  c <- makeChannel

  -- Start 5 readers
  readerThreads <-
    for [1..5] $ \_ => do
      tid <- fork (reader c)
      usleep 10000
      pure tid

  () <- usleep 10000

  -- Start 5 producers
  p1 <- fork $ producer c 0
  p2 <- fork $ producer c 1
  p3 <- fork $ producer c 2
  p4 <- fork $ producer c 3
  p5 <- fork $ producer c 4

  -- Wait for all readers and producers
  threadWait p1
  threadWait p2
  threadWait p3
  threadWait p4
  threadWait p5
  ignore $ traverse (\t => threadWait t) readerThreads

