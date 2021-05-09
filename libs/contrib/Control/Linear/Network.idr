module Control.Linear.Network

-- An experimental linear type based API to sockets

import public Data.Either
import public Data.Maybe

import Control.Linear.LIO

import public Network.Socket.Data
import Network.Socket

public export
data SocketState = Ready | Bound | Listening | Open | Closed

||| Define the domain of SocketState transitions.
||| Label every such transition.
public export
data Action : SocketState -> Type where
  Bind    : Action Ready
  Listen  : Action Bound
  Accept  : Action Listening
  Send    : Action Open
  Receive : Action Open
  Close   : Action st

export
data Socket : SocketState -> Type where
     MkSocket : Socket.Data.Socket -> Socket st

||| For every label of a SocketState transition
||| and a success value of the transition,
||| define its result.
public export
Next : (action : Action st)
    -> (success : Bool)
    -> Type
Next Bind    True  = Socket Bound
Next Listen  True  = Socket Listening
Next Accept  True  = LPair (Socket Listening) (Socket Open)
Next Send    True  = Socket Open
Next Receive True  = Socket Open
Next Close   True  = Socket Closed
Next _       False = Socket Closed

export
newSocket : LinearIO io
      => (fam  : SocketFamily)
      -> (ty   : SocketType)
      -> (pnum : ProtocolNumber)
      -> (success : (1 sock : Socket Ready) -> L io ())
      -> (fail : SocketError -> L io ())
      -> L io ()
newSocket fam ty pnum success fail
    = do Right rawsock <- socket fam ty pnum
               | Left err => fail err
         success (MkSocket rawsock)

export
close : LinearIO io => (1 sock : Socket st) -> L1 io (Socket Closed)
close (MkSocket sock)
    = do Socket.close sock
         pure1 (MkSocket sock)

export
done : LinearIO io => (1 sock : Socket Closed) -> L io ()
done (MkSocket sock) = pure ()

export
bind : LinearIO io =>
       (1 sock : Socket Ready) ->
       (addr : Maybe SocketAddress) ->
       (port : Port) ->
       L1 io (Res (Maybe SocketError)
         (\res => Next Bind (isNothing res)))
bind (MkSocket sock) addr port
    = do code <- Socket.bind sock addr port
         case code of
           0 =>
             pure1 $ Nothing # MkSocket sock
           err =>
             pure1 $ Just err # MkSocket sock

export
connect : LinearIO io =>
          (sock : Socket) ->
          (addr : SocketAddress) ->
          (port : Port) ->
          L1 io (Res (Maybe SocketError)
            (\case Nothing => Socket Ready
                   Just _  => Socket Closed))
connect sock addr port
    = do code <- Socket.connect sock addr port
         case code of
           0 =>
             pure1 $ Nothing # MkSocket sock
           err =>
             pure1 $ Just err # MkSocket sock

export
listen : LinearIO io =>
         (1 sock : Socket Bound) ->
         L1 io (Res (Maybe SocketError)
           (\res => Next Listen (isNothing res)))
listen (MkSocket sock)
    = do code <- Socket.listen sock
         case code of
           0 =>
             pure1 $ Nothing # MkSocket sock
           err =>
             pure1 $ Just err # MkSocket sock


export
accept : LinearIO io =>
         (1 sock : Socket Listening) ->
         L1 io (Res (Maybe SocketError)
           (\res => Next Accept (isNothing res)))
accept (MkSocket sock)
    = do Right (sock', sockaddr) <- Socket.accept sock
             | Left err => pure1 (Just err # MkSocket sock)
         pure1 (Nothing # (MkSocket sock # MkSocket sock'))

export
send : LinearIO io =>
       (1 sock : Socket Open) ->
       (msg : String) ->
       L1 io (Res (Maybe SocketError)
         (\res => Next Send (isNothing res)))
send (MkSocket sock) msg
    = do Right c <- Socket.send sock msg
             | Left err => pure1 (Just err # MkSocket sock)
         pure1 (Nothing # MkSocket sock)

export
recv : LinearIO io =>
       (1 sock : Socket Open) ->
       (len : ByteLength) ->
       L1 io (Res (Either SocketError (String, ResultCode))
         (\res => Next Receive (isRight res)))
recv (MkSocket sock) len
    = do Right msg <- Socket.recv sock len
             | Left err => pure1 (Left err # MkSocket sock)
         pure1 (Right msg # MkSocket sock)

export
recvAll : LinearIO io =>
          (1 sock : Socket Open) ->
          L1 io (Res (Either SocketError String)
            (\res => Next Receive (isRight res)))
recvAll (MkSocket sock)
    = do Right msg <- Socket.recvAll sock
             | Left err => pure1 (Left err # MkSocket sock)
         pure1 (Right msg # MkSocket sock)
