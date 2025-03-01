module System.File.Process

import public System.Escape
import public System.File.Error
import public System.File.Mode
import System.FFI
import System.File.Support
import public System.File.Types

%foreign "C:fflush,libc 6"
         "node:lambda:()=>0"
prim__flush : FilePtr -> PrimIO Int
%foreign supportC "idris2_popen"
         supportNode "popen"
prim__popen : String -> String -> PrimIO FilePtr
%foreign supportC "idris2_pclose"
         supportNode "pclose"
prim__pclose : FilePtr -> PrimIO Int

data Popen2Result : Type where [external]

%foreign supportC "idris2_popen2"
prim__popen2 : String -> PrimIO (Ptr Popen2Result)

%foreign supportC "idris2_popen2WaitByPid"
covering -- significantly non-total
prim__popen2WaitByPid : Int -> PrimIO Int
%foreign supportC "idris2_popen2WaitByHandler"
covering -- significantly non-total
prim__popen2WaitByHandler : AnyPtr -> PrimIO Int

%foreign supportC "idris2_popen2ChildPid"
prim__popen2ChildPid : Ptr Popen2Result -> PrimIO Int

%foreign supportC "idris2_popen2ChildHandler"
prim__popen2ChildHandler : Ptr Popen2Result -> PrimIO AnyPtr

%foreign supportC "idris2_popen2FileIn"
prim__popen2FileIn : Ptr Popen2Result -> PrimIO FilePtr

%foreign supportC "idris2_popen2FileOut"
prim__popen2FileOut : Ptr Popen2Result -> PrimIO FilePtr

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
||| IMPORTANT: The NodeJS backend only currently supports the Read mode. Also with
|||            the NodeJS backend, the opened process will finish execution before
|||            popen returns (it blocks on open) which is different than other
|||            backends which will block on close.
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


||| Wait for the process associated with the pipe to terminate.
|||
||| @ fh the file handle to the stream to close/wait on
export
pclose : HasIO io => (fh : File) -> io Int
pclose (FHandle h) = primIO (prim__pclose h)

||| Result of a popen2 command, containing the
public export
record SubProcess where
  constructor MkSubProcess
  ||| Process id of the spawned process
  pid : Int
  ||| The way to manipulate the spawned process, for systems where pid is not enough for this
  handler : AnyPtr
  ||| The input stream of the spawned process
  input : File
  ||| The output stream of the spawned process
  output : File

||| Create a new bidirectional pipe by invoking the shell, which is passed the
||| given command-string using the '-c' flag, in a new process. On success
||| a SubProcess is returned which holds the process id and file handles
||| for input and output.
||| You should call `popen2Wait` after you've done with the child process
||| in order to clean up all system resources.
|||
||| IMPORTANT: You may deadlock if write to a process which is waiting to flush
|||            its output.  It is recommended to read and write from separate threads.
|||
||| This function is not supported on node at this time.
export
popen2 : HasIO io => (cmd : String) -> io (Either FileError SubProcess)
popen2 cmd = do
  ptr <- primIO (prim__popen2 cmd)
  if prim__nullPtr ptr /= 0
    then returnError
    else do
      pid <- primIO (prim__popen2ChildPid ptr)
      handle <- primIO (prim__popen2ChildHandler ptr)
      input <- primIO (prim__popen2FileIn ptr)
      output <- primIO (prim__popen2FileOut ptr)
      free (prim__forgetPtr ptr)
      pure $ Right (MkSubProcess pid handle (FHandle input) (FHandle output))

||| Blocks and waits until the process created by `popen2` finished
|||
||| This function relates to `popen2` like `pclose` relates to `popen`.
||| Returns exit code of the process being waited.
||| IMPORTANT: this function mustn't be called twice for the same argument.
|||
||| Support of this function in the backends must be the same as for `popen2`.
export
covering -- significantly non-total
popen2Wait : HasIO io => SubProcess -> io Int
popen2Wait sp = primIO $
  if prim__nullAnyPtr sp.handler /= 0
    then prim__popen2WaitByPid sp.pid
    else prim__popen2WaitByHandler sp.handler

namespace Escaped
  export
  popen : HasIO io => (cmd : List String) -> (m : Mode) -> io (Either FileError File)
  popen = popen . escapeCmd

  export
  popen2 : HasIO io => (cmd : List String) -> io (Either FileError SubProcess)
  popen2 = popen2 . escapeCmd
