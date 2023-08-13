module Libraries.System.File.Meta

import System.File.Handle
import System.File.Support
import public System.File.Types

%default total

%foreign supportC "idris2_fileAccessTimeNs"
prim__fileAccessTimeNs : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileModifiedTimeNs"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).mtimeMs * 1000000 % 1000000000"
prim__fileModifiedTimeNs : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileStatusTimeNs"
prim__fileStatusTimeNs : FilePtr -> PrimIO Int

||| Get the nanosecond part of File's atime.
export
fileAccessTimeNs : HasIO io => (h : File) -> io (Either FileError Int)
fileAccessTimeNs (FHandle f)
    = do res <- primIO (prim__fileAccessTimeNs f)
         if res > 0
            then ok res
            else returnError

||| Get the nanosecond part of File's mtime.
export
fileModifiedTimeNs : HasIO io => (h : File) -> io (Either FileError Int)
fileModifiedTimeNs (FHandle f)
    = do res <- primIO (prim__fileModifiedTimeNs f)
         if res > 0
            then ok res
            else returnError

||| Get the nanosecond part of File's ctime.
export
fileStatusTimeNs : HasIO io => (h : File) -> io (Either FileError Int)
fileStatusTimeNs (FHandle f)
    = do res <- primIO (prim__fileStatusTimeNs f)
         if res > 0
            then ok res
            else returnError

