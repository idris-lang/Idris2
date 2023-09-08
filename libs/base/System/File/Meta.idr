||| Functions for accessing file metadata.
module System.File.Meta

import Data.String

import System.FFI

import System.File.Handle
import System.File.Support
import public System.File.Types

%default total

||| Pointer to a structure holding File's time attributes
FileTimePtr : Type
FileTimePtr = AnyPtr

%foreign supportC "idris2_fileSize"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).size"
prim__fileSize : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileSize"
prim__fPoll : FilePtr -> PrimIO Int

%foreign supportC "idris2_fileTime"
         "node:support:filetime,support_system_file"
prim__fileTime : FilePtr -> PrimIO FileTimePtr

%foreign supportC "idris2_filetimeAccessTimeSec"
         "node:lambda:ft=>ft.atime_sec"
prim__filetimeAccessTimeSec : FileTimePtr -> PrimIO Int

%foreign supportC "idris2_filetimeAccessTimeNsec"
         "node:lambda:ft=>ft.atime_nsec"
prim__filetimeAccessTimeNsec : FileTimePtr -> PrimIO Int

%foreign supportC "idris2_filetimeModifiedTimeSec"
         "node:lambda:ft=>ft.mtime_sec"
prim__filetimeModifiedTimeSec : FileTimePtr -> PrimIO Int

%foreign supportC "idris2_filetimeModifiedTimeNsec"
         "node:lambda:ft=>ft.mtime_nsec"
prim__filetimeModifiedTimeNsec : FileTimePtr -> PrimIO Int

%foreign supportC "idris2_filetimeStatusTimeSec"
         "node:lambda:ft=>ft.ctime_sec"
prim__filetimeStatusTimeSec : FileTimePtr -> PrimIO Int

%foreign supportC "idris2_filetimeStatusTimeNsec"
         "node:lambda:ft=>ft.ctime_nsec"
prim__filetimeStatusTimeNsec : FileTimePtr -> PrimIO Int

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

||| Record that holds timestamps with nanosecond precision
public export
record Timestamp where
  constructor MkTimestamp
  sec  : Int
  nsec : Int

export
Eq Timestamp where
  t == t' = (t.sec == t'.sec) && (t.nsec == t'.nsec)

export
Ord Timestamp where
  t < t' = (t.sec < t'.sec) || (t.sec == t'.sec && t.nsec < t'.nsec)

export
Show Timestamp where
  show t = "\{show t.sec}.\{padLeft 9 '0' $ show t.nsec}"

||| Record that holds file's time attributes
public export
record FileTime where
  constructor MkFileTime
  atime : Timestamp
  mtime : Timestamp
  ctime : Timestamp

||| Get File's time attributes
export
fileTime : HasIO io => (h : File) -> io (Either FileError FileTime)
fileTime (FHandle f)
    = do res <- primIO (prim__fileTime f)
         ft <- parseFileTime res
         free res
         if ft.atime.sec > 0
            then ok ft
            else returnError
    where
      parseFileTime : FileTimePtr -> io FileTime
      parseFileTime ft = pure $ MkFileTime { atime = MkTimestamp { sec  = !(primIO (prim__filetimeAccessTimeSec ft))
                                                                 , nsec = !(primIO (prim__filetimeAccessTimeNsec ft))
                                                                 }
                                           , mtime = MkTimestamp { sec  = !(primIO (prim__filetimeModifiedTimeSec ft))
                                                                 , nsec = !(primIO (prim__filetimeModifiedTimeNsec ft))
                                                                 }
                                           , ctime = MkTimestamp { sec  = !(primIO (prim__filetimeStatusTimeSec ft))
                                                                 , nsec = !(primIO (prim__filetimeStatusTimeNsec ft))
                                                                 }
                                           }

||| Get the File's atime.
export
fileAccessTime : HasIO io => (h : File) -> io (Either FileError Int)
fileAccessTime h = (fileTime h <&> (.atime.sec)) @{Compose}

||| Get the File's mtime.
export
fileModifiedTime : HasIO io => (h : File) -> io (Either FileError Int)
fileModifiedTime h = (fileTime h <&> (.mtime.sec)) @{Compose}

||| Get the File's ctime.
export
fileStatusTime : HasIO io => (h : File) -> io (Either FileError Int)
fileStatusTime h = (fileTime h <&> (.ctime.sec)) @{Compose}

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

