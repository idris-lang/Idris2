||| Low-Level C Sockets bindings for Idris. Used by higher-level, cleverer things.
||| Types used by Network.Socket.Raw and Network.Socket.
|||
||| Original (C) SimonJF, MIT Licensed, 2014
||| Modified (C) The Idris Community, 2015, 2016, 2019
module Network.Socket.Data

import Data.List
import Data.List1
import Data.Strings

-- ------------------------------------------------------------ [ Type Aliases ]

public export
ByteLength : Type
ByteLength = Int

public export
ResultCode : Type
ResultCode = Int

||| Protocol Number.
|||
||| Generally good enough to just set it to 0.
public export
ProtocolNumber : Type
ProtocolNumber = Int

||| SocketError: Error thrown by a socket operation
public export
SocketError : Type
SocketError = Int

||| SocketDescriptor: Native C Socket Descriptor
public export
SocketDescriptor : Type
SocketDescriptor = Int

public export
Port : Type
Port = Int

-- --------------------------------------------------------------- [ Constants ]

||| Backlog used within listen() call -- number of incoming calls
export
BACKLOG : Int
BACKLOG = 20

-- Repeat to avoid a dependency cycle
%foreign "C:idrnet_geteagain,libidris2_support"
prim__idrnet_geteagain : PrimIO Int

export
EAGAIN : Int
EAGAIN =
  -- I'm sorry
  -- maybe
  unsafePerformIO $ primIO $ prim__idrnet_geteagain

-- ---------------------------------------------------------------- [ Error Code ]

-- repeat without export to avoid dependency cycles
%foreign "C:idrnet_errno,libidris2_support"
prim__idrnet_errno : PrimIO Int

%foreign "C:isNull,libidris2_support"
prim__idrnet_isNull : (ptr : AnyPtr) -> PrimIO Int


export
getErrno : HasIO io => io SocketError
getErrno = primIO $ prim__idrnet_errno

export
nullPtr : HasIO io => AnyPtr -> io Bool
nullPtr p = do 0 <- primIO  $ prim__idrnet_isNull p
               | _ => pure True
               pure False

-- -------------------------------------------------------------- [ Interfaces ]

public export
interface ToCode a where
  toCode : a -> Int

-- --------------------------------------------------------- [ Socket Families ]

||| Socket Families
|||
||| The ones that people might actually use. We're not going to need US
||| Government proprietary ones.
public export
data SocketFamily : Type where
  ||| Unspecified
  AF_UNSPEC : SocketFamily

  ||| Unix type sockets
  AF_UNIX : SocketFamily

  ||| IP / UDP etc. IPv4
  AF_INET : SocketFamily

  |||  IP / UDP etc. IPv6
  AF_INET6 : SocketFamily

Show SocketFamily where
  show AF_UNSPEC = "AF_UNSPEC"
  show AF_UNIX   = "AF_UNIX"
  show AF_INET   = "AF_INET"
  show AF_INET6  = "AF_INET6"

-- This is a bit of a hack to get the OS-dependent magic constants out of C and
-- into Idris without having to faff around on the preprocessor on the Idris
-- side.
%foreign "C:idrnet_af_unspec,libidris2_support"
prim__idrnet_af_unspec : PrimIO Int

%foreign "C:idrnet_af_unix,libidris2_support"
prim__idrnet_af_unix : PrimIO Int

%foreign "C:idrnet_af_inet,libidris2_support"
prim__idrnet_af_inet : PrimIO Int

%foreign "C:idrnet_af_inet6,libidris2_support"
prim__idrnet_af_inet6 : PrimIO Int

export
ToCode SocketFamily where
  toCode AF_UNSPEC = unsafePerformIO $ primIO $ prim__idrnet_af_unspec
  toCode AF_UNIX   = unsafePerformIO $ primIO $ prim__idrnet_af_unix
  toCode AF_INET   = unsafePerformIO $ primIO $ prim__idrnet_af_inet
  toCode AF_INET6  = unsafePerformIO $ primIO $ prim__idrnet_af_inet6

export
getSocketFamily : Int -> Maybe SocketFamily
getSocketFamily i =
    lookup i [ (toCode AF_UNSPEC, AF_UNSPEC)
             , (toCode AF_UNIX, AF_UNIX)
             , (toCode AF_INET, AF_INET)
             , (toCode AF_INET6, AF_INET6)
             ]

-- ------------------------------------------------------------ [ Socket Types ]

||| Socket Types.
public export
data SocketType : Type where
  ||| Not a socket, used in certain operations
  NotASocket : SocketType

  ||| TCP
  Stream : SocketType

  ||| UDP
  Datagram : SocketType

  ||| Raw sockets
  RawSocket : SocketType

export
Show SocketType where
  show NotASocket = "Not a socket"
  show Stream     = "Stream"
  show Datagram   = "Datagram"
  show RawSocket  = "Raw"

export
ToCode SocketType where
  toCode NotASocket = 0
  toCode Stream     = 1
  toCode Datagram   = 2
  toCode RawSocket  = 3

-- --------------------------------------------------------------- [ Addresses ]

||| Network Addresses
public export
data SocketAddress : Type where
  IPv4Addr : Int -> Int -> Int -> Int -> SocketAddress

  ||| Not implemented (yet)
  IPv6Addr : SocketAddress

  Hostname : String -> SocketAddress

  ||| Used when there's a parse error
  InvalidAddress : SocketAddress

export
Show SocketAddress where
  show (IPv4Addr i1 i2 i3 i4) = concat $ intersperse "." (map show [i1, i2, i3, i4])
  show IPv6Addr               = "NOT IMPLEMENTED YET"
  show (Hostname host)        = host
  show InvalidAddress         = "Invalid"

||| Parses a textual representation of an IPv4 address into a SocketAddress
export
parseIPv4 : String -> SocketAddress
parseIPv4 str =
    case splitted of
      (i1 ::: i2 :: i3 :: i4 :: _) => IPv4Addr i1 i2 i3 i4
      _ => InvalidAddress
  where
    toInt' : String -> Integer
    toInt' = cast

    toInt : String -> Int
    toInt s = fromInteger $ toInt' s

    splitted : List1 Int
    splitted = map toInt (split (\c => c == '.') str)

-- --------------------------------------------------------- [ UDP Information ]

-- TODO: Expand to non-string payloads
public export
record UDPRecvData where
  constructor MkUDPRecvData
  remote_addr : SocketAddress
  remote_port : Port
  recv_data   : String
  data_len    : Int

public export
record UDPAddrInfo where
  constructor MkUDPAddrInfo
  remote_addr : SocketAddress
  remote_port : Port

-- ----------------------------------------------------------------- [ Sockets ]
||| The metadata about a socket
public export
record Socket where
  constructor MkSocket
  descriptor     : SocketDescriptor
  family         : SocketFamily
  socketType     : SocketType
  protocolNumber : ProtocolNumber
