import System.Concurrency

-- Test that put/get works for multiple values.
main : IO ()
main =
  do c <- makeChannel
     t <- fork $ ignore (for [0..2] $ \n => channelPut c n)
     v0 <- channelGet c
     v1 <- channelGet c
     v2 <- channelGet c
     threadWait t
     if v0 == 0 && v1 == 1 && v2 == 2
        then putStrLn "Success!"
        else putStrLn "At least one value changed in transmission."
