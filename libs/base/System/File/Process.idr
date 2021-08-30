module System.File.Process

import public System.File.Error
import public System.File.Mode
import System.File.Support
import public System.File.Types

%foreign "C:fflush,libc 6"
prim__flush : FilePtr -> PrimIO Int
%foreign support "idris2_popen"
prim__popen : String -> String -> PrimIO FilePtr
%foreign support "idris2_pclose"
prim__pclose : FilePtr -> PrimIO ()

export
fflush : HasIO io => (h : File) -> io ()
fflush (FHandle f)
    = ignore $ primIO (prim__flush f)

export
popen : HasIO io => String -> Mode -> io (Either FileError File)
popen f m = do
    ptr <- primIO (prim__popen f (modeStr m))
    if prim__nullAnyPtr ptr /= 0
        then returnError
        else pure (Right (FHandle ptr))

export
pclose : HasIO io => File -> io ()
pclose (FHandle h) = primIO (prim__pclose h)
