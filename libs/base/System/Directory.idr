module System.Directory

import System.Errno
import public System.File

%default total

public export
DirPtr : Type
DirPtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support, idris_directory.h"

ok : HasIO io => a -> io (Either FileError a)
ok x = pure (Right x)

%foreign support "idris2_currentDirectory"
         "node:lambda:()=>process.cwd()"
prim__currentDir : PrimIO (Ptr String)

%foreign support "idris2_changeDir"
         "node:support:changeDir,support_system_directory"
prim__changeDir : String -> PrimIO Int

%foreign support "idris2_createDir"
         "node:support:createDir,support_system_directory"
prim__createDir : String -> PrimIO Int

%foreign support "idris2_openDir"
prim__openDir : String -> PrimIO DirPtr

%foreign support "idris2_closeDir"
prim__closeDir : DirPtr -> PrimIO ()

%foreign support "idris2_removeDir"
prim__removeDir : String -> PrimIO ()

%foreign support "idris2_nextDirEntry"
prim__dirEntry : DirPtr -> PrimIO (Ptr String)

export
data Directory : Type where
     MkDir : DirPtr -> Directory

export
createDir : HasIO io => String -> io (Either FileError ())
createDir dir
    = do res <- primIO (prim__createDir dir)
         if res == 0
            then ok ()
            else returnError

export
changeDir : HasIO io => String -> io Bool
changeDir dir
    = do ok <- primIO (prim__changeDir dir)
         pure (ok == 0)

export
currentDir : HasIO io => io (Maybe String)
currentDir
    = do res <- primIO prim__currentDir
         if prim__nullPtr res /= 0
            then pure Nothing
            else pure (Just (prim__getString res))

export
openDir : HasIO io => String -> io (Either FileError Directory)
openDir d
    = do res <- primIO (prim__openDir d)
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (MkDir res)

export
closeDir : HasIO io => Directory -> io ()
closeDir (MkDir d) = primIO (prim__closeDir d)

export
removeDir : HasIO io => String -> io ()
removeDir dirName = primIO (prim__removeDir dirName)

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

collectDir : HasIO io => Directory -> io (Either FileError (List String))
collectDir d
    = liftIO $ do let (>>=) : (IO . Either e) a -> (a -> (IO . Either e) b) -> (IO . Either e) b
                      (>>=) = Prelude.(>>=) @{Monad.Compose {m = IO} {t = Either e}}
                  Just n <- nextDirEntry d
                    | Nothing => pure $ Right []
                  ns <- assert_total $ collectDir d
                  pure $ Right (n :: ns)

export
listDir : HasIO io => String -> io (Either FileError (List String))
listDir name = do Right d <- openDir name
                    | Left e => pure $ Left e
                  ns <- collectDir d
                  ignore <- closeDir d
                  pure $ ns
