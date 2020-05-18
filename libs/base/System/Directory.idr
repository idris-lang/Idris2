module System.Directory

import public System.File

public export
DirPtr : Type
DirPtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign support "idris2_fileErrno"
prim_fileErrno : PrimIO Int

returnError : IO (Either FileError a)
returnError
    = do err <- primIO prim_fileErrno
         case err of
              0 => pure $ Left FileReadError
              1 => pure $ Left FileWriteError
              2 => pure $ Left FileNotFound
              3 => pure $ Left PermissionDenied
              4 => pure $ Left FileExists
              _ => pure $ Left (GenericFileError (err-5))

ok : a -> IO (Either FileError a)
ok x = pure (Right x)

%foreign support "idris2_currentDirectory"
prim_currentDir : PrimIO (Ptr String)

%foreign support "idris2_changeDir"
prim_changeDir : String -> PrimIO Int

%foreign support "idris2_createDir"
prim_createDir : String -> PrimIO Int

%foreign support "idris2_dirOpen"
prim_openDir : String -> PrimIO DirPtr

%foreign support "idris2_dirClose"
prim_closeDir : DirPtr -> PrimIO ()

%foreign support "idris2_nextDirEntry"
prim_dirEntry : DirPtr -> PrimIO (Ptr String)

export
data Directory : Type where
     MkDir : DirPtr -> Directory

export
createDir : String -> IO (Either FileError ())
createDir dir
    = do res <- primIO (prim_createDir dir)
         if res == 0
            then ok ()
            else returnError

export
changeDir : String -> IO Bool
changeDir dir
    = do ok <- primIO (prim_changeDir dir)
         pure (ok == 0)

export
currentDir : IO (Maybe String)
currentDir
    = do res <- primIO prim_currentDir
         if prim__nullPtr res /= 0
            then pure Nothing
            else pure (Just (prim__getString res))

export
dirOpen : String -> IO (Either FileError Directory)
dirOpen d
    = do res <- primIO (prim_openDir d)
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (MkDir res)

export
dirClose : Directory -> IO ()
dirClose (MkDir d) = primIO (prim_closeDir d)

export
dirEntry : Directory -> IO (Either FileError String)
dirEntry (MkDir d)
    = do res <- primIO (prim_dirEntry d)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)
