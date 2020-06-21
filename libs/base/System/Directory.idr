module System.Directory

import public System.File

public export
DirPtr : Type
DirPtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

js_try_catch_lasterr_Int : String -> String
js_try_catch_lasterr_Int x = "{try{" ++ x ++ ";return 0n}catch(e){process.__lasterr = e; return 1n}}"

%foreign support "idris2_fileErrno"
         "node:lambda:()=>{const n = process.__lasterr.errno; switch(n){case -17: return 4n; default: return -BigInt(n)}}"
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
         "node:lambda:()=>process.cwd()"
prim_currentDir : PrimIO (Ptr String)

%foreign support "idris2_changeDir"
         ("node:lambda:d=>" ++ js_try_catch_lasterr_Int "process.chdir(d)")
prim_changeDir : String -> PrimIO Int

%foreign support "idris2_createDir"
         ("node:lambdaRequire:fs:d=>" ++ js_try_catch_lasterr_Int "__require_fs.mkdirSync(d)")
prim_createDir : String -> PrimIO Int

%foreign support "idris2_openDir"
prim_openDir : String -> PrimIO DirPtr

%foreign support "idris2_closeDir"
prim_closeDir : DirPtr -> PrimIO ()

%foreign support "idris2_removeDir"
prim_removeDir : String -> PrimIO ()

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
openDir : String -> IO (Either FileError Directory)
openDir d
    = do res <- primIO (prim_openDir d)
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (MkDir res)

export
closeDir : Directory -> IO ()
closeDir (MkDir d) = primIO (prim_closeDir d)

export
removeDir : String -> IO ()
removeDir dirName = primIO (prim_removeDir dirName)

export
dirEntry : Directory -> IO (Either FileError String)
dirEntry (MkDir d)
    = do res <- primIO (prim_dirEntry d)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)
