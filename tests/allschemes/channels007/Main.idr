import System.Concurrency
import System

-- Test that using channelGetNonBlocking works as expected.
main : IO ()
main = do
  chan <- makeChannel
  threadID <- fork $ do
    channelPut chan "Hello"
  sleep 1
  case !(channelGetNonBlocking chan) of
    Nothing   =>
      putStrLn "Nothing"
    Just val' =>
      putStrLn val'
  sleep 1

