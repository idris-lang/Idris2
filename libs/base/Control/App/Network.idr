module Control.App.Network

import Control.App
import Control.App.Network.Data

data SocketState = Ready | Bound | Listening | Open | Closed

data Socket : SocketState -> Type where
     MkSocket : Int -> Socket s

data NetworkError = Foo

interface Has [Exception NetworkError] e => Network e where
  newSocket : (1 p : (1 s : Socket Ready) -> App e a) -> App e a
  done : (1 s : Socket Closed) -> App e ()

bind : (1 sock : Socket Ready) ->
       (addr : Maybe SocketAddress) -> (port : Port) ->
       Either NetworkError (Socket Bound)

{-
connect : (sock : Socket) -> (addr : SocketAddress) -> (port : Port) -> IO ResultCode
listen : (sock : Socket) -> IO Int
accept : (sock : Socket) -> IO (Either SocketError (Socket, SocketAddress))
send : (sock : Socket) -> (msg  : String) -> IO (Either SocketError ResultCode)
recv : (sock : Socket) -> (len : ByteLength) -> IO (Either SocketError (String, ResultCode))
close : Socket -> IO ()
-}
