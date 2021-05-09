module System.Directory

import public System.File

public export
DirPtr : Type
DirPtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign support "idris2_fileErrno"
         "node:support:fileErrno,support_system_file"
prim__fileErrno : PrimIO Int

returnError : HasIO io => io (Either FileError a)
returnError
    = do err <- primIO prim__fileErrno
         case err of
              0 => pure $ Left FileReadError
              1 => pure $ Left FileWriteError
              2 => pure $ Left FileNotFound
              3 => pure $ Left PermissionDenied
              4 => pure $ Left FileExists
              _ => pure $ Left (GenericFileError (err-5))

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
dirEntry : HasIO io => Directory -> io (Either FileError String)
dirEntry (MkDir d)
    = do res <- primIO (prim__dirEntry d)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)
