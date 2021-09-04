module System.File.Error

import System.Errno

import System.File.Support
import public System.File.Types

%default total

%foreign support "idris2_fileError"
         "node:lambda:x=>(x===1?1:0)"
prim__error : FilePtr -> PrimIO Int

%foreign support "idris2_fileErrno"
         "node:support:fileErrno,support_system_file"
prim__fileErrno : PrimIO Int

public export
data FileError = GenericFileError Int -- errno
               | FileReadError
               | FileWriteError
               | FileNotFound
               | PermissionDenied
               | FileExists

export
returnError : HasIO io => io (Either FileError a)
returnError
    = do err <- primIO prim__fileErrno
         pure $ Left $
           case err of
              0 => FileReadError
              1 => FileWriteError
              2 => FileNotFound
              3 => PermissionDenied
              4 => FileExists
              _ => GenericFileError (err-5)

export
Show FileError where
  show (GenericFileError errno) = strerror errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

export
fileError : HasIO io => File -> io Bool
fileError (FHandle f)
    = do x <- primIO $ prim__error f
         pure (x /= 0)
