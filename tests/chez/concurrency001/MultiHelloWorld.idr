module MultiHelloWorld

import Data.List
import System
import System.Concurrency

futureHelloWorld : (Int, String) -> Future Unit
futureHelloWorld (us, n) = forkIO $ do
  usleep us
  putStrLn $ "Hello " ++ n ++ "!"

simpleIO : IO (List Unit)
simpleIO = do
  let futures = futureHelloWorld <$> [(3000, "World"), (1000, "Bar"), (0, "Foo"), (2000, "Idris")]
  let awaited = await <$> futures
  pure awaited
