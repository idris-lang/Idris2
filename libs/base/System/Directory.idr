||| Directory access and handling.
module System.Directory

import System.Errno
import public System.File
import System.FFI

%default total

public export
DirPtr : Type
DirPtr = AnyPtr

||| Shorthand for referring to the C support library
|||
||| @ fn the function name to refer to in the C support library
supportC : (fn : String) -> String
supportC fn = "C:\{fn}, libidris2_support, idris_directory.h"

||| Shorthand for referring to the Node system support library
|||
||| @ fn the function name to refer to in the js/system_support.js file
supportNode : (fn : String) -> String
supportNode fn = "node:support:\{fn},support_system_directory"

ok : HasIO io => a -> io (Either FileError a)
ok x = pure (Right x)

%foreign supportC "idris2_currentDirectory"
         "node:lambda:()=>process.cwd()"
prim__currentDir : PrimIO (Ptr String)

%foreign supportC "idris2_changeDir"
         supportNode "changeDir"
prim__changeDir : String -> PrimIO Int

%foreign supportC "idris2_createDir"
         supportNode "createDir"
prim__createDir : String -> PrimIO Int

%foreign supportC "idris2_openDir"
         supportNode "openDir"
prim__openDir : String -> PrimIO DirPtr

%foreign supportC "idris2_closeDir"
         supportNode "closeDir"
prim__closeDir : DirPtr -> PrimIO ()

%foreign supportC "idris2_removeDir"
         supportNode "removeDir"
prim__removeDir : String -> PrimIO ()

%foreign supportC "idris2_nextDirEntry"
         supportNode "dirEntry"
prim__dirEntry : DirPtr -> PrimIO (Ptr String)

||| Data structure for managing the pointer to a directory.
export
data Directory : Type where
     MkDir : DirPtr -> Directory

||| Try to create a directory at the specified path.
export
createDir : HasIO io => String -> io (Either FileError ())
createDir dir
    = do res <- primIO (prim__createDir dir)
         if res == 0
            then ok ()
            else returnError

||| Change the current working directory to the specified path. Returns whether
||| the operation succeeded.
export
changeDir : HasIO io => String -> io Bool
changeDir dir
    = do ok <- primIO (prim__changeDir dir)
         pure (ok == 0)

||| Get the absolute path of the current working directory. Returns `Nothing` if
||| an error occurred.
export
currentDir : HasIO io => io (Maybe String)
currentDir
    = do res <- primIO prim__currentDir
         if prim__nullPtr res /= 0
            then pure Nothing
            else do let s = prim__getString res
                    free $ prim__forgetPtr res
                    pure (Just s)

||| Try to open the directory at the specified path.
export
openDir : HasIO io => String -> io (Either FileError Directory)
openDir d
    = do res <- primIO (prim__openDir d)
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (MkDir res)

||| Close the given `Directory`.
export
closeDir : HasIO io => Directory -> io ()
closeDir (MkDir d) = primIO (prim__closeDir d)

||| Remove the directory at the specified path.
||| If the directory is not empty, this operation fails.
export
removeDir : HasIO io => String -> io ()
removeDir dirName = primIO (prim__removeDir dirName)

||| Get the next entry in the `Directory`, omitting the '.' and '..' entries.
export
nextDirEntry : HasIO io => Directory -> io (Either FileError (Maybe String))
nextDirEntry (MkDir d)
    = do res <- primIO (prim__dirEntry d)
         if prim__nullPtr res /= 0
            then if !(getErrno) /= 0
                    then returnError
                    else pure $ Right Nothing
            else do let n = prim__getString res
                    if n == "." || n == ".."
                       then assert_total $ nextDirEntry (MkDir d)
                       else pure $ Right (Just n)

||| Get a list of all the entries in the `Directory`, excluding the '.' and '..'
||| entries.
collectDir : HasIO io => Directory -> io (Either FileError (List String))
collectDir d
    = liftIO $ do let (>>=) : (IO . Either e) a -> (a -> (IO . Either e) b) -> (IO . Either e) b
                      (>>=) = Prelude.(>>=) @{Monad.Compose {m = IO} {t = Either e}}
                  Just n <- nextDirEntry d
                    | Nothing => pure $ Right []
                  ns <- assert_total $ collectDir d
                  pure $ Right (n :: ns)

||| Get a list of all the entries in the directory at the specified path,
||| excluding the '.' and '..' entries.
|||
||| @ name the directory to list
export
listDir : HasIO io => (name : String) -> io (Either FileError (List String))
listDir name = do Right d <- openDir name
                    | Left e => pure $ Left e
                  ns <- collectDir d
                  ignore <- closeDir d
                  pure $ ns
