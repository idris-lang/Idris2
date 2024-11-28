import System.Concurrency
import System

-- Test that using channelGetNonBlocking works as expected.
main : IO ()
main = do
  chan <- makeChannel
  threadID <- fork $ do
    channelPut chan "Hello"
    channelPut chan "Goodbye"
  sleep 1
  case !(channelGetNonBlocking chan) of
    Nothing   =>
      putStrLn "Nothing"
    Just val' =>
      putStrLn val'
  case !(channelGetNonBlocking chan) of
    Nothing   =>
      putStrLn "Nothing"
    Just val' =>
      putStrLn val'
  sleep 1

