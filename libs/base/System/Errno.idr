||| Managing error codes.
module System.Errno

%default total

%foreign "C:idris2_getErrno, libidris2_support, idris_support.h"
prim__getErrno : PrimIO Int

%foreign "C:idris2_strerror, libidris2_support, idris_support.h"
         "node:lambda:errno=>'Error code: '+errno"
prim__strerror : Int -> PrimIO String

||| Fetch libc `errno` global variable.
export
getErrno : HasIO io => io Int
getErrno = primIO prim__getErrno

||| Convert numeric `errno` to string.
export
strerror : Int -> String
strerror errno = unsafePerformIO $ primIO $ prim__strerror errno
