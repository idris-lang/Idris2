module System.File.Handle

import public System.File.Error
import public System.File.Mode
import System.File.Support
import public System.File.Types

%default total

%foreign supportC "idris2_openFile"
         supportNode "openFile"
prim__open : String -> String -> PrimIO FilePtr

%foreign supportC "idris2_closeFile"
         "node:lambda:(fp) => require('fs').closeSync(fp.fd)"
prim__close : FilePtr -> PrimIO ()

||| Open the given file name with the specified mode.
|||
||| @ f the file name to open
||| @ m the mode to open the file with
export
openFile : HasIO io => (f : String) -> (m : Mode) -> io (Either FileError File)
openFile f m
    = do res <- primIO (prim__open f (modeStr m))
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (FHandle res)

||| Close the given file handle.
|||
||| @ fh the file handle to close
export
closeFile : HasIO io => (fh : File) -> io ()
closeFile (FHandle f) = primIO (prim__close f)

||| Perform a given operation on successful file open
||| and ensure the file is closed afterwards or perform
||| a different operation if the file fails to open.
export
withFile : HasIO io => (filename : String) ->
                       Mode ->
                       (onError : FileError -> io a) ->
                       (onOpen  : File -> io (Either a b)) ->
                       io (Either a b)
withFile filename mode onError onOpen =
  do Right h <- openFile filename mode
       | Left err => Left <$> onError err
     res <- onOpen h
     closeFile h
     pure res
