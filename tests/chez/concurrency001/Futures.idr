module Futures

import Data.List
import Data.So
import System
import System.Future
import System.Info

constant : IO ()
constant = do
  let a = await $ fork "String"
  putStrLn a

partial
futureHelloWorld : (Int, String) -> IO (Future Unit)
futureHelloWorld (us, n) with (choose (us >= 0))
  futureHelloWorld (us, n) | Left p = forkIO $ do
    if (os == "darwin") then sleep (us `div` 1000) else usleep us
    putStrLn $ "Hello " ++ n ++ "!"

partial
simpleIO : IO (List Unit)
simpleIO = do
  futures <- sequence $ futureHelloWorld <$> [(3000, "World"), (1000, "Bar"), (0, "Foo"), (2000, "Idris")]
  let awaited = await <$> futures
  pure awaited
