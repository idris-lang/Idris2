module Main

import System
import System.Info
import System.File
import Network.Socket
import Network.Socket.Data
import Network.Socket.Raw

testSocket : String
testSocket = "./idris2_test.socket"

runServer : (net : Bool) -> IO (Either String (if net then Port else ()))
runServer net = do
  Right sock <- socket (if net then AF_INET else AF_UNIX) Stream 0
        | Left fail => pure (Left $ "Failed to open socket: " ++ show fail)
  res <- bind sock (Just (Hostname (if net then "localhost" else testSocket))) 0
  if res /= 0
    then pure (Left $ "Failed to bind socket with error: " ++ show res)
    else do
      port <- if net then getSockPort sock else pure ()
      res <- listen sock
      if res /= 0
         then pure . Left $ "Failed to listen on socket with error: " ++ show res
         else do ignore $ fork (serve sock)
                 pure $ Right port
  where
    serve : Socket -> IO ()
    serve sock = do
      Right (s, _) <- accept sock
        | Left err => putStrLn ("Failed to accept on socket with error: " ++ show err)
      Right  (str, _) <- recv s 1024
        | Left err => putStrLn ("Failed to accept on socket with error: " ++ show err)
      putStrLn ("Received: " ++ str)
      Right n <- send s ("echo: " ++ str)
        | Left err => putStrLn ("Server failed to send data with error: " ++ show err)
      pure ()

runClient : (net : Bool) -> Port -> IO ()
runClient net serverPort = do
  Right sock <- socket (if net then AF_INET else AF_UNIX) Stream 0
    | Left fail => putStrLn ("Failed to open socket: " ++ show fail)
  res <- connect sock (Hostname $ if net then "localhost" else testSocket) serverPort
  if res /= 0
    then putStrLn ("Failed to connect client to port " ++ show serverPort ++ ": " ++ show res)
    else do
      Right n <- send sock ("hello world from a " ++ (if net then "ipv4" else "unix") ++ " socket!")
        | Left err => putStrLn ("Client failed to send data with error: " ++ show err)
      Right (str, _) <- recv sock 1024
        | Left err => putStrLn ("Client failed to receive on socket with error: " ++ show err)
      -- assuming that stdout buffers get flushed in between system calls, this is "guaranteed"
      -- to be printed after the server prints its own message
      putStrLn ("Received: " ++ str)

main : IO ()
main = do
  Right serverPort <- runServer True
    | Left err => putStrLn $ "[server] " ++ err
  runClient True serverPort
  Right () <- runServer False
    | Left err => putStrLn $ "[server] " ++ err
  runClient False 0
  ignore $ removeFile testSocket
