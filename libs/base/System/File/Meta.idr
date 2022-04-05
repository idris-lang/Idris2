||| Functions for accessing file metadata.
module System.File.Meta

import System.File.Handle
import System.File.Support
import public System.File.Types

%default total

%foreign supportC "idris2_fileSize"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).size"
prim__fileSize : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileSize"
prim__fPoll : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileAccessTime"
prim__fileAccessTime : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileModifiedTime"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).mtimeMs / 1000"
prim__fileModifiedTime : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileStatusTime"
prim__fileStatusTime : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileIsTTY"
         "node:lambda:fp=>Number(require('tty').isatty(fp.fd))"
prim__fileIsTTY : FilePtr -> PrimIO Int

||| Check if a file exists for reading.
export
exists : HasIO io => String -> io Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

||| Pick the first existing file
export
firstExists : HasIO io => List String -> io (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

||| Get the File's atime.
export
fileAccessTime : HasIO io => (h : File) -> io (Either FileError Int)
fileAccessTime (FHandle f)
    = do res <- primIO (prim__fileAccessTime f)
         if res > 0
            then ok res
            else returnError

||| Get the File's mtime.
export
fileModifiedTime : HasIO io => (h : File) -> io (Either FileError Int)
fileModifiedTime (FHandle f)
    = do res <- primIO (prim__fileModifiedTime f)
         if res > 0
            then ok res
            else returnError

||| Get the File's ctime.
export
fileStatusTime : HasIO io => (h : File) -> io (Either FileError Int)
fileStatusTime (FHandle f)
    = do res <- primIO (prim__fileStatusTime f)
         if res > 0
            then ok res
            else returnError

||| Get the File's size.
export
fileSize : HasIO io => (h : File) -> io (Either FileError Int)
fileSize (FHandle f)
    = do res <- primIO (prim__fileSize f)
         if res >= 0
            then ok res
            else returnError

||| Check whether the given File's size is non-zero.
export
fPoll : HasIO io => File -> io Bool
fPoll (FHandle f)
    = do p <- primIO (prim__fPoll f)
         pure (p > 0)

||| Check whether the given File is a terminal device.
export
isTTY : HasIO io => (h : File) -> io Bool
isTTY (FHandle f) = (/= 0) <$> primIO (prim__fileIsTTY f)

