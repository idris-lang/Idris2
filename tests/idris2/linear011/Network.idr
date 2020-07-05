import Control.Linear.LIO

import Network.Socket

data SocketState = Ready | Bound | Listening | Open | Closed

data Socket : SocketState -> Type where
     MkSocket : Socket.Data.Socket -> Socket st

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

bind : LinearIO io =>
       (1 _ : Socket Ready) ->
       (addr : Maybe SocketAddress) ->
       (port : Port) ->
       L io {use=1} (Res Bool (\res => Socket (case res of
                                                    False => Closed
                                                    True => Bound)))
bind (MkSocket sock) addr port
    = do ok <- Socket.bind sock addr port
         if ok == 0
            then pure1 (True # ?foo1)
            else pure1 (False # ?foo2)
