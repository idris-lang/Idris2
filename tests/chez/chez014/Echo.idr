module Main

import System
import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

%cg chez libidris_net

runServer : IO (Either String (Port, ThreadID))
runServer = do
  Right sock <- socket AF_INET Stream 0
        | Left fail => pure (Left $ "Failed to open socket: " ++ show fail)
  res <- bind sock (Just (Hostname "localhost")) 0
  if res /= 0
    then pure (Left $ "Failed to bind socket with error: " ++ show res)
    else do
      port <- getSockPort sock
      res <- listen sock
      if res /= 0
        then pure (Left $ "Failed to listen on socket with error: " ++ show res)
        else do
          forked <- fork (serve port sock)
          pure $ Right (port, forked)

  where
    serve : Port -> Socket -> IO ()
    serve port sock = do
      Right (s, _) <- accept sock
        | Left err => putStrLn ("Failed to accept on socket with error: " ++ show err)
      Right  (str, _) <- recv s 1024
        | Left err => putStrLn ("Failed to accept on socket with error: " ++ show err)
      putStrLn ("Received: " ++ str)
      Right n <- send s ("echo: " ++ str)
        | Left err => putStrLn ("Server failed to send data with error: " ++ show err)
      pure ()

runClient : Port -> IO ()
runClient serverPort = do
  Right sock <- socket AF_INET Stream 0
    | Left fail => putStrLn ("Failed to open socket: " ++ show fail)
  res <- connect sock (Hostname "localhost") serverPort
  if res /= 0
    then putStrLn ("Failed to connect client to port " ++ show serverPort ++ ": " ++ show res)
    else do
      Right n <- send sock ("hello world!")
        | Left err => putStrLn ("Client failed to send data with error: " ++ show err)
      Right (str, _) <- recv sock 1024
        | Left err => putStrLn ("Client failed to receive on socket with error: " ++ show err)
      -- assuming that stdout buffers get flushed in between system calls, this is "guaranteed"
      -- to be printed after the server prints its own message
      putStrLn ("Received: " ++ str)

main : IO ()
main = do
  Right (serverPort, tid) <- runServer
    | Left err => putStrLn $ "[server] " ++ err
  runClient serverPort
