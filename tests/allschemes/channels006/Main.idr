module Main

import System
import System.Concurrency
import System.Info

-- Taken from tests/chez/futures001

-- Issue in MacOS brew chez related to clock ( https://github.com/Homebrew/homebrew-core/pull/10159 )
-- Windows seems to be really flaky with usleep
extraSleep : (us : Int) -> So (us >= 0) => IO ()
extraSleep us =
  if (os == "darwin" || isWindows)
    then sleep (us `div` 10000)
    else usleep us

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
         extraSleep 10000

consumer : Channel Nat -> IO ()
consumer ch =
  do recv
     recv
     recv
     recv
  where
    recv : IO ()
    recv =
      do extraSleep 20000
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
