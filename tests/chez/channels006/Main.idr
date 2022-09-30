module Main

import System
import System.Concurrency

producer : Channel Nat -> IO ()
producer ch =
  do send 1
     send 2
     send 3
     send 4
     where
       send : Nat -> IO ()
       send i =
         do putStrLn $ "> " ++ show i
            channelPut ch i

consumer : Channel Nat -> IO ()
consumer ch =
  do recv
     recv
     recv
     recv
     where
       recv : IO ()
       recv =
         do usleep 100000
            v <- channelGet ch
            putStrLn $ "< " ++ show v

main : IO ()
main =
  do ch <- makeChannel
     p <- fork $ producer ch
     c <- fork $ consumer ch
     threadWait c
     threadWait p
     putStrLn "done"

