module Control.Linear.Network

-- An experimental linear type based API to sockets

import Control.Linear.LIO

import public Network.Socket.Data
import Network.Socket

public export
data SocketState = Ready | Bound | Listening | Open | Closed

export
data Socket : SocketState -> Type where
     MkSocket : Socket.Data.Socket -> Socket st

export
newSocket : LinearIO io
      => (fam  : SocketFamily)
      -> (ty   : SocketType)
      -> (pnum : ProtocolNumber)
      -> (success : (1 _ : Socket Ready) -> L io ())
      -> (fail : SocketError -> L io ())
      -> L io ()
newSocket fam ty pnum success fail
    = do Right rawsock <- socket fam ty pnum
               | Left err => fail err
         success (MkSocket rawsock)

export
close : LinearIO io => (1 _ : Socket st) -> L io {use=1} (Socket Closed)
close (MkSocket sock)
    = do Socket.close sock
         pure1 (MkSocket sock)

export
done : LinearIO io => (1 _ : Socket Closed) -> L io ()
done (MkSocket sock) = pure ()

export
bind : LinearIO io =>
       (1 _ : Socket Ready) ->
       (addr : Maybe SocketAddress) ->
       (port : Port) ->
       L io {use=1} (Res Bool (\res => Socket (case res of
                                                    False => Closed
                                                    True => Bound)))
bind (MkSocket sock) addr port
    = do ok <- Socket.bind sock addr port
         pure1 $ ok == 0 # MkSocket sock

export
connect : LinearIO io =>
          (sock : Socket) ->
          (addr : SocketAddress) ->
          (port : Port) ->
          L io {use=1} (Res Bool (\res => Socket (case res of
                                                       False => Closed
                                                       True => Open)))
connect sock addr port
    = do ok <- Socket.connect sock addr port
         pure1 $ ok == 0 # MkSocket sock

export
listen : LinearIO io =>
         (1 _ : Socket Bound) ->
         L io {use=1} (Res Bool (\res => Socket (case res of
                                                      False => Closed
                                                      True => Listening)))
listen (MkSocket sock)
    = do ok <- Socket.listen sock
         pure1 $ ok == 0 # MkSocket sock

export
accept : LinearIO io =>
         (1 _ : Socket Listening) ->
         L io {use=1} (Res Bool (\case
                                    False => Socket Listening
                                    True => (Socket Listening, Socket Open)))
accept (MkSocket sock)
    = do Right (sock', sockaddr) <- Socket.accept sock
             | Left err => pure1 (False # MkSocket sock)
         pure1 (True # (MkSocket sock, MkSocket sock'))

export
send : LinearIO io =>
       (1 _ : Socket Open) ->
       (msg : String) ->
       L io {use=1} (Res Bool (\res => Socket (case res of
                                                    False => Closed
                                                    True => Open)))
send (MkSocket sock) msg
    = do Right c <- Socket.send sock msg
             | Left err => pure1 (False # MkSocket sock)
         pure1 (True # MkSocket sock)

export
recv : LinearIO io =>
       (1 _ : Socket Open) ->
       (len : ByteLength) ->
       L io {use=1} (Res (Maybe (String, ResultCode))
                         (\res => Socket (case res of
                                               Nothing => Closed
                                               Just msg => Open)))
recv (MkSocket sock) len
    = do Right msg <- Socket.recv sock len
             | Left err => pure1 (Nothing # MkSocket sock)
         pure1 (Just msg # MkSocket sock)

export
recvAll : LinearIO io =>
          (1 _ : Socket Open) ->
          L io {use=1} (Res (Maybe String)
                            (\res => Socket (case res of
                                                  Nothing => Closed
                                                  Just msg => Open)))
recvAll (MkSocket sock)
    = do Right msg <- Socket.recvAll sock
             | Left err => pure1 (Nothing # MkSocket sock)
         pure1 (Just msg # MkSocket sock)
