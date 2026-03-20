module TestSocket

import Network.Socket
import Network.Socket.Data

||| Test that socket creation and close work for both TCP and UDP.
testCreate : IO ()
testCreate = do
  Right tcp <- socket AF_INET Stream 0
    | Left err => putStrLn $ "FAIL: TCP socket: " ++ show err
  Right udp <- socket AF_INET Datagram 0
    | Left err => putStrLn $ "FAIL: UDP socket: " ++ show err
  close tcp
  close udp
  putStrLn "create+close: OK"

||| Test UDP sendTo / recvFrom over loopback.
testUDPLoopback : IO ()
testUDPLoopback = do
  Right sender <- socket AF_INET Datagram 0
    | Left err => putStrLn $ "FAIL: sender socket: " ++ show err
  Right receiver <- socket AF_INET Datagram 0
    | Left err => putStrLn $ "FAIL: receiver socket: " ++ show err

  -- Bind receiver to loopback on an ephemeral port
  0 <- bind receiver (Just $ IPv4Addr 127 0 0 1) 54321
    | err => putStrLn $ "FAIL: bind: " ++ show err

  Right bytesSent <- sendTo sender (IPv4Addr 127 0 0 1) 54321 "hello"
    | Left err => putStrLn $ "FAIL: sendTo: " ++ show err

  Right (_, payload, _) <- recvFrom receiver 1024
    | Left err => putStrLn $ "FAIL: recvFrom: " ++ show err

  close sender
  close receiver

  putStrLn $ "udp loopback: " ++ if payload == "hello" then "OK" else "FAIL (got " ++ payload ++ ")"

main : IO ()
main = do
  testCreate
  testUDPLoopback
