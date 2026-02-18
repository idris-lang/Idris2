import Data.List
import System.Concurrency

consumer : Channel Nat -> IO ()
consumer c =
  do (S k) <- channelGet c
      | Z => pure ()
     consumer c

producer : Channel Nat -> IO ()
producer c = ignore $ traverse (\n => channelPut c n) [1..100]

nConsumers : Nat
nConsumers = 3

nProducers : Nat
nProducers = 5

main : IO ()
main =
  do c <- makeChannel
     cTIDs <- for (replicate nConsumers 0) $ \_ => fork (consumer c)
     pTIDs <- for (replicate nProducers 0) $ \_ => fork (producer c)
     ignore $ traverse (\t => threadWait t) pTIDs
     ignore $ for (replicate nConsumers 0) $ \_ => channelPut c Z
     ignore $ traverse (\t => threadWait t) cTIDs
     putStrLn "SUCCESS!!!"
