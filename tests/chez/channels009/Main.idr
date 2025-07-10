import Data.Maybe
import System
import System.Concurrency

-- One reader
reader : Channel Nat -> IO ()
reader c = do
  val <- channelGetWithTimeout c 300
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

  -- Start 5 readers first
  readerThreads <-
    for [1..5] $ \_ =>
      fork (reader c)

  -- Start 3 producers (too late for 5 readers)
  p1 <- fork $ producer c 0
  p2 <- fork $ producer c 1
  p3 <- fork $ producer c 2

  -- Wait for all readers and producers
  threadWait p1
  threadWait p2
  threadWait p3
  ignore $ traverse (\t => threadWait t) readerThreads

