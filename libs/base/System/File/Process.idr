module System.File.Process

import public System.Escape
import public System.File.Error
import public System.File.Mode
import System.File.Support
import public System.File.Types

%foreign "C:fflush,libc 6"
prim__flush : FilePtr -> PrimIO Int
%foreign supportC "idris2_popen"
prim__popen : String -> String -> PrimIO FilePtr
%foreign supportC "idris2_pclose"
prim__pclose : FilePtr -> PrimIO Int

||| Force a write of all user-space buffered data for the given `File`.
|||
||| @ h the file handle to flush
export
fflush : HasIO io => (h : File) -> io ()
fflush (FHandle f)
    = ignore $ primIO (prim__flush f)

||| Create a new unidirectional pipe by invoking the shell, which is passed the
||| given command-string using the '-c' flag, in a new process. The pipe is
||| opened with the given mode.
|||
||| @ cmd the command to pass to the shell
||| @ m   the mode the pipe should have
export
popen : HasIO io => (cmd : String) -> (m : Mode) -> io (Either FileError File)
popen cmd m = do
    ptr <- primIO (prim__popen cmd (modeStr m))
    if prim__nullAnyPtr ptr /= 0
        then returnError
        else pure (Right (FHandle ptr))

namespace Escaped
  export
  popen : HasIO io => (cmd : List String) -> (m : Mode) -> io (Either FileError File)
  popen = popen . escapeCmd

||| Wait for the process associated with the pipe to terminate.
|||
||| @ fh the file handle to the stream to close/wait on
export
pclose : HasIO io => (fh : File) -> io Int
pclose (FHandle h) = primIO (prim__pclose h)
