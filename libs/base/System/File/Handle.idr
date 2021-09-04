module System.File.Handle

import public System.File.Error
import public System.File.Mode
import System.File.Support
import public System.File.Types

%default total

%foreign support "idris2_openFile"
         "node:support:openFile,support_system_file"
prim__open : String -> String -> PrimIO FilePtr

%foreign support "idris2_closeFile"
         "node:lambda:(fp) => require('fs').closeSync(fp.fd)"
prim__close : FilePtr -> PrimIO ()

export
openFile : HasIO io => String -> Mode -> io (Either FileError File)
openFile f m
    = do res <- primIO (prim__open f (modeStr m))
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (FHandle res)

export
closeFile : HasIO io => File -> io ()
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
