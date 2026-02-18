import System.Concurrency

-- Simple looping thread
consumer : Channel Nat -> IO ()
consumer c =
  do (S k) <- channelGet c
      | Z => pure ()
     consumer c

--  Test that using the same channel with multiple consumers is okay.
main : IO ()
main =
  do c <- makeChannel
     tids <- for [1..7] $ \_ => fork (consumer c)
     ignore $ for [1..100] $ \_ => channelPut c 1
     ignore $ for [1..7] $ \_ => channelPut c Z
     ignore $ traverse (\t => threadWait t) tids
     putStrLn "Success!"
