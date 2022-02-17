||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016, 2019
module Network.Socket

import public Network.Socket.Data
import Network.Socket.Raw
import Network.FFI
import Data.Buffer
import Data.List
import Data.SnocList

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

recvAllRec : (Monoid a, HasIO io) => io (Either SocketError a) -> SnocList a -> io (Either SocketError a)
recvAllRec recv_from_socket acc = case !recv_from_socket of
  Left 0 => pure (Right $ concat acc)
  Left c => pure (Left c)
  Right str => recvAllRec recv_from_socket (acc :< str)

||| Receive all the remaining data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success the payload `String`
|||
||| @sock The socket on which to receive the message.
export
recvAll : HasIO io => (sock : Socket) -> io (Either SocketError String)
recvAll sock = recvAllRec {a=String} (mapSnd fst <$> recv sock 65536) [<]

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

||| Send data on the specified socket.
|||
||| Returns on failure a `SocketError`.
||| Returns on success the number of bytes sent.
|||
||| @sock   The socket on which to send the message.
||| @bytes  The data to send.
export
sendBytes : HasIO m => Socket -> List Bits8 -> m (Either SocketError Int)
sendBytes sock bytes = do
  let len' = cast $ length bytes
  Just buffer <- newBuffer len'
  | Nothing => assert_total $ idris_crash "somehow newBuffer failed"
  traverse_ (uncurry (setBits8 buffer)) (zip [0..len'] bytes)
  ret <- primIO $ prim__idrnet_send_bytes sock.descriptor buffer len' 0
  case ret < 0 of
    True => pure $ Left ret
    False => pure $ Right ret

||| Receive data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success a pairing of:
||| + `List Bits8` :: The payload.
||| + `ResultCode` :: The result of the underlying function.
|||
||| @sock     The socket on which to receive the message.
||| @max_size How much of the data to receive at most.
export
recvBytes : HasIO m => Socket -> (max_size : ByteLength) -> m (Either SocketError (List Bits8))
recvBytes sock max_size = do
  Just buffer <- newBuffer max_size
  | Nothing => pure $ Left (-1)
  ret <- primIO $ prim__idrnet_recv_bytes sock.descriptor buffer max_size 0
  case ret > 0 of
    False => do
      pure $ Left ret
    True => do
      bytes <- traverse (getBits8 buffer) [0..((cast ret)-1)]
      pure $ Right $ toList bytes


||| Receive all the remaining data on the specified socket.
|||
||| Returns on failure a `SocketError`
||| Returns on success the payload `List Bits8`
|||
||| @sock The socket on which to receive the message.
export
recvAllBytes : HasIO io => (sock : Socket) -> io (Either SocketError (List Bits8))
recvAllBytes sock = recvAllRec {a=List Bits8} (recvBytes sock 65536) [<]
