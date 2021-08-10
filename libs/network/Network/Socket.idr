||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016, 2019
module Network.Socket

import public Network.Socket.Data
import Network.Socket.Raw
import Data.List
import Network.FFI

-- ----------------------------------------------------- [ Network Socket API. ]

||| Creates a UNIX socket with the given family, socket type and protocol
||| number. Returns either a socket or an error.
export
socket : HasIO io
      => (fam  : SocketFamily)
      -> (ty   : SocketType)
      -> (pnum : ProtocolNumber)
      -> io (Either SocketError Socket)
socket sf st pn = do
  socket_res <- primIO $ prim__idrnet_socket (toCode sf) (toCode st) pn

  if socket_res == -1
    then map Left getErrno
    else pure $ Right (MkSocket socket_res sf st pn)

||| Close a socket
export
close : HasIO io => Socket -> io ()
close sock = do _ <- primIO $ prim__idrnet_close $ descriptor sock
                pure ()

||| Binds a socket to the given socket address and port.
||| Returns 0 on success, an error code otherwise.
export
bind : HasIO io
    => (sock : Socket)
    -> (addr : Maybe SocketAddress)
    -> (port : Port)
    -> io Int
bind sock addr port = do
    bind_res <- primIO $ prim__idrnet_bind
                  (descriptor sock)
                  (toCode $ family sock)
                  (toCode $ socketType sock)
                  (saString addr)
                  port

    if bind_res == (-1)
      then getErrno
      else pure 0
  where
    saString : Maybe SocketAddress -> String
    saString (Just sa) = show sa
    saString Nothing   = ""

||| Connects to a given address and port.
||| Returns 0 on success, and an error number on error.
export
connect : HasIO io
       => (sock : Socket)
       -> (addr : SocketAddress)
       -> (port : Port)
       -> io ResultCode
connect sock addr port = do
  conn_res <- primIO $ prim__idrnet_connect
              (descriptor sock) (toCode $ family sock) (toCode $ socketType sock) (show addr) port

  if conn_res == (-1)
    then getErrno
    else pure 0

||| Listens on a bound socket.
|||
||| @sock The socket to listen on.
export
listen : HasIO io => (sock : Socket) -> io Int
listen sock = do
  listen_res <- primIO $ prim__idrnet_listen (descriptor sock) BACKLOG
  if listen_res == (-1)
    then getErrno
    else pure 0

||| Accept a connection on the provided socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `Socket`        :: The socket representing the connection.
||| + `SocketAddress` :: The
|||
||| @sock The socket used to establish connection.
export
accept : HasIO io
      => (sock : Socket)
      -> io (Either SocketError (Socket, SocketAddress))
accept sock = do

  -- We need a pointer to a sockaddr structure. This is then passed into
  -- idrnet_accept and populated. We can then query it for the SocketAddr and free it.

  sockaddr_ptr <- primIO prim__idrnet_create_sockaddr

  accept_res <- primIO $ prim__idrnet_accept (descriptor sock) sockaddr_ptr
  if accept_res == (-1)
    then map Left getErrno
    else do
      let (MkSocket _ fam ty p_num) = sock
      sockaddr <- getSockAddr (SAPtr sockaddr_ptr)
      sockaddr_free (SAPtr sockaddr_ptr)
      pure $ Right ((MkSocket accept_res fam ty p_num), sockaddr)

||| Send data on the specified socket.
|||
||| Returns on failure a `SocketError`.
||| Returns on success the `ResultCode`.
|||
||| @sock The socket on which to send the message.
||| @msg  The data to send.
export
send : HasIO io
    => (sock : Socket)
    -> (msg  : String)
    -> io (Either SocketError ResultCode)
send sock dat = do
  send_res <- primIO $ prim__idrnet_send (descriptor sock) dat

  if send_res == (-1)
    then map Left getErrno
    else pure $ Right send_res

||| Receive data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `String`     :: The payload.
||| + `ResultCode` :: The result of the underlying function.
|||
||| @sock The socket on which to receive the message.
||| @len  How much of the data to receive.
export
recv : HasIO io
    => (sock : Socket)
    -> (len : ByteLength)
    -> io (Either SocketError (String, ResultCode))
recv sock len = do
  -- Firstly make the request, get some kind of recv structure which
  -- contains the result of the recv and possibly the retrieved payload
  recv_struct_ptr <- primIO $ prim__idrnet_recv (descriptor sock) len
  recv_res <- primIO $ prim__idrnet_get_recv_res recv_struct_ptr

  if recv_res == (-1)
    then do
      errno <- getErrno
      freeRecvStruct (RSPtr recv_struct_ptr)
      pure $ Left errno
    else
      if recv_res == 0
        then do
           freeRecvStruct (RSPtr recv_struct_ptr)
           pure $ Left 0
        else do
           payload <- primIO $ prim__idrnet_get_recv_payload recv_struct_ptr
           freeRecvStruct (RSPtr recv_struct_ptr)
           pure $ Right (payload, recv_res)

||| Receive all the remaining data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success the payload `String`
|||
||| @sock The socket on which to receive the message.
export
recvAll : HasIO io => (sock : Socket) -> io (Either SocketError String)
recvAll sock = recvRec sock [] 64
  where
    partial
    recvRec : Socket -> List String -> ByteLength -> io (Either SocketError String)
    recvRec sock acc n = do res <- recv sock n
                            case res of
                              Left c => pure (Left c)
                              Right (str, res) => let n' = min (n * 2) 65536 in
                                                  if res < n then pure (Right $ concat $ reverse $ str :: acc)
                                                  else recvRec sock (str :: acc) n'

||| Send a message.
|||
||| Returns on failure a `SocketError`
||| Returns on success the `ResultCode`
|||
||| @sock The socket on which to send the message.
||| @addr Address of the recipient.
||| @port The port on which to send the message.
||| @msg  The message to send.
export
sendTo : HasIO io
      => (sock : Socket)
      -> (addr : SocketAddress)
      -> (port : Port)
      -> (msg  : String)
      -> io (Either SocketError ByteLength)
sendTo sock addr p dat = do
  sendto_res <- primIO $ prim__idrnet_sendto
                (descriptor sock) dat (show addr) p (toCode $ family sock)

  if sendto_res == (-1)
    then map Left getErrno
    else pure $ Right sendto_res

||| Receive a message.
|||
||| Returns on failure a `SocketError`.
||| Returns on success a triple of
||| + `UDPAddrInfo` :: The address of the sender.
||| + `String`      :: The payload.
||| + `Int`         :: Result value from underlying function.
|||
||| @sock The channel on which to receive.
||| @len  Size of the expected message.
|||
export
recvFrom : HasIO io
        => (sock : Socket)
        -> (len  : ByteLength)
        -> io (Either SocketError (UDPAddrInfo, String, ResultCode))
recvFrom sock bl = do
  recv_ptr <- primIO $ prim__idrnet_recvfrom
                       (descriptor sock) bl

  let recv_ptr' = RFPtr recv_ptr
  isNull <- (nullPtr recv_ptr)
  if isNull
    then map Left getErrno
    else do
      result <- primIO $ prim__idrnet_get_recvfrom_res recv_ptr
      if result == -1
        then do
          freeRecvfromStruct recv_ptr'
          map Left getErrno
        else do
          payload <- foreignGetRecvfromPayload recv_ptr'
          port <- foreignGetRecvfromPort recv_ptr'
          addr <- foreignGetRecvfromAddr recv_ptr'
          freeRecvfromStruct recv_ptr'
          pure $ Right (MkUDPAddrInfo addr port, payload, result)
