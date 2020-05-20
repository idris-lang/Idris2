||| FFI binding to the low-Level C Sockets bindings for Idris. 
||| 
||| Modified (C) The Idris Community, 2020
module Network.FFI

import Network.Socket.Data

-- From sys/socket.h

%foreign "C:close,idris_net"
export
socket_close : (sockdes : SocketDescriptor) -> PrimIO Int

%foreign "C:listen,idris_net"
export
socket_listen : (sockfd : SocketDescriptor) -> (backlog : Int) -> PrimIO Int


-- From idris_net.h

%foreign "C:idrnet_socket,idris_net"
export
idrnet_socket : (domain, type, protocol : Int) -> PrimIO Int

%foreign "C:idrnet_bind,idris_net"
export
idrnet_bind : (sockfd : SocketDescriptor) -> (family, socket_type : Int) -> (host : String) 
            -> (port : Port) -> PrimIO Int
            
%foreign "C:idrnet_connect,idris_net"
export
idrnet_connect : (sockfd : SocketDescriptor) -> (family, socket_type : Int) -> (host : String) 
               -> (port : Port) -> PrimIO Int

%foreign "C:idrnet_sockaddr_family,idris_net"
export
idrnet_sockaddr_family : (sockaddr : AnyPtr) -> PrimIO Int

%foreign "C:idrnet_sockaddr_ipv4,idris_net"
export
idrnet_sockaddr_ipv4 : (sockaddr : AnyPtr) -> PrimIO String

%foreign "C:idrnet_sockaddr_ipv4_port,idris_net"
export
idrnet_sockaddr_ipv4_port : (sockaddr : AnyPtr) -> PrimIO Int

%foreign "C:idrnet_sockaddr_port,idris_net"
export
idrnet_sockaddr_port : (sockfd : SocketDescriptor) -> PrimIO Int


%foreign "C:idrnet_create_sockaddr,idris_net"
export
idrnet_create_sockaddr : PrimIO AnyPtr

%foreign "C:idrnet_accept,idris_net"
export
idrnet_accept : (sockfd : SocketDescriptor) -> (sockaddr : AnyPtr) -> PrimIO Int

%foreign "C:idrnet_send,idris_net"
export
idrnet_send : (sockfd : SocketDescriptor) -> (dataString : String) -> PrimIO Int

%foreign "C:idrnet_send_buf,idris_net"
export
idrnet_send_buf : (sockfd : SocketDescriptor) -> (dataBuffer : AnyPtr) -> (len : Int) -> PrimIO Int


%foreign "C:idrnet_recv,idris_net"
export
idrnet_recv : (sockfd : SocketDescriptor) -> (len : Int) -> PrimIO AnyPtr

%foreign "C:idrnet_recv_buf,idris_net"
export
idrnet_recv_buf : (sockfd : SocketDescriptor) -> (buf : AnyPtr) -> (len : Int) 
               -> PrimIO Int

%foreign "C:idrnet_sendto,idris_net"
export
idrnet_sendto : (sockfd : SocketDescriptor) -> (dataString,host : String)
             -> (port : Port) -> (family : Int) -> PrimIO Int

%foreign "C:idrnet_sendto_buf,idris_net"
export
idrnet_sendto_buf : (sockfd : SocketDescriptor) -> (dataBuf : AnyPtr) -> (buf_len : Int) 
                 -> (host : String) -> (port : Port) -> (family : Int) -> PrimIO Int
                 
%foreign "C:idrnet_recvfrom,idris_net"
export
idrnet_recvfrom : (sockfd : SocketDescriptor) -> (len : Int) -> PrimIO AnyPtr                 

%foreign "C:idrnet_recvfrom_buf,idris_net"
export
idrnet_recvfrom_buf : (sockfd : SocketDescriptor) -> (buf : AnyPtr) -> (len : Int) 
                   -> PrimIO AnyPtr                 

%foreign "C:idrnet_get_recv_res,idris_net"
export
idrnet_get_recv_res : (res_struct : AnyPtr) -> PrimIO Int

%foreign "C:idrnet_get_recv_payload,idris_net"
export
idrnet_get_recv_payload : (res_struct : AnyPtr) -> PrimIO String

%foreign "C:idrnet_free_recv_struct,idris_net"
export
idrnet_free_recv_struct : (res_struct : AnyPtr) -> PrimIO ()

%foreign "C:idrnet_get_recvfrom_res,idris_net"
export
idrnet_get_recvfrom_res : (res_struct : AnyPtr) -> PrimIO Int

%foreign "C:idrnet_get_recvfrom_payload,idris_net"
export
idrnet_get_recvfrom_payload : (res_struct : AnyPtr) -> PrimIO String

%foreign "C:idrnet_get_recvfrom_sockaddr,idris_net"
export
idrnet_get_recvfrom_sockaddr : (res_struct : AnyPtr) -> PrimIO AnyPtr

%foreign "C:idrnet_free_recvfrom_struct,idris_net"
export
idrnet_free_recvfrom_struct : (res_struct : AnyPtr) -> PrimIO ()


%foreign "C:idrnet_geteagain,idris_net"
export
idrnet_geteagain : PrimIO Int

%foreign "C:idrnet_errno,idris_net"
export
idrnet_errno : PrimIO Int

%foreign "C:idrnet_malloc,idris_net"
export
idrnet_malloc : (size : Int) -> PrimIO AnyPtr

%foreign "C:idrnet_free,idris_net"
export
idrnet_free : (ptr : AnyPtr) -> PrimIO ()

%foreign "C:idrnet_peek,idris_net"
export
idrnet_peek : (ptr : AnyPtr) -> (offset : {-Unsigned-} Int) -> PrimIO {-Unsigned-} Int

%foreign "C:idrnet_poke,idris_net"
export
idrnet_poke : (ptr : AnyPtr) -> (offset : {-Unsigned-} Int) -> (val : Int {- should be Char? -}) 
           -> PrimIO ()
