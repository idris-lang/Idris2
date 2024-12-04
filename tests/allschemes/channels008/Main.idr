import System
import System.Concurrency

-- Simple producing thread.
producer : Channel String -> IO ()
producer c = ignore $ loop 2
  where
    loop : Nat -> IO ()
    loop Z     = pure ()
    loop (S n) = do
      channelPut c $ show n
      sleep 1
      loop (minus n 1)

-- Test that channelGetWithTimeout works as expected.
main : IO ()
main =
  do c    <- makeChannel
     tids <- for [0..1] $ \_ => fork $ producer c
     sleep 5
     vals <- for [0..1] $ \_ => channelGetWithTimeout c 5 
     ignore $ traverse (\t => threadWait t) tids
     for_ vals $ \val =>
       case val of
         Nothing   =>
           putStrLn "Nothing"
         Just val' =>
           putStrLn val'
     {-
     let s = sum vals
     if s == 50500
        then putStrLn "Success!"
        else putStrLn "How did we get here?"
     -}

