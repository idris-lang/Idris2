import System.Concurrency

-- Simple producing thread.
producer : Channel Nat -> IO ()
producer c = ignore $ for [1..100] $ \n => channelPut c n

-- Test that using the same channel with multiple producers is okay.
main : IO ()
main =
  do c <- makeChannel
     tids <- for [1..10] $ \_ => fork (producer c)
     vals <- for [1..1000] $ \_ => channelGet c
     ignore $ traverse (\t => threadWait t) tids
     let s = sum vals
     if s == 50500
        then putStrLn "Success!"
        else putStrLn "How did we get here?"
