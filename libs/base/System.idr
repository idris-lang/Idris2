module System

import public Data.So
import Data.String

import public System.Escape
import System.File

%default total

||| Shorthand for referring to the C support library
|||
||| @ fn the function name to refer to in the C support library
supportC : (fn : String) -> String
supportC fn = "C:\{fn}, libidris2_support, idris_support.h"

||| Shorthand for referring to the Node system support library
|||
||| @ fn the function name to refer to in the js/system_support.js file
supportNode : (fn : String) -> String
supportNode fn = "node:support:\{fn},support_system"

||| Shorthand for referring to libc 6
|||
||| @ fn the function name to refer to in libc 6
libc : (fn : String) -> String
libc fn = "C:" ++ fn ++ ", libc 6"

-- `sleep` and `usleep` need to be tied to `blodwen-[u]sleep` for threading
-- reasons (see support/racket/support.rkt)

%foreign "scheme,racket:blodwen-sleep"
         supportC "idris2_sleep"
prim__sleep : Int -> PrimIO ()

%foreign "scheme,racket:blodwen-usleep"
         supportC "idris2_usleep"
prim__usleep : Int -> PrimIO ()

||| Sleep for the specified number of seconds or, if signals are supported,
||| until an un-ignored signal arrives.
||| The exact wall-clock time slept might slighly differ depending on how busy
||| the system is and the resolution of the system's clock.
|||
||| @ sec the number of seconds to sleep for
export
sleep : HasIO io => (sec : Int) -> io ()
sleep sec = primIO (prim__sleep sec)

||| Sleep for the specified number of microseconds or, if signals are supported,
||| until an un-ignored signal arrives.
||| The exact wall-clock time slept might slighly differ depending on how busy
||| the system is and the resolution of the system's clock.
|||
||| @ usec the number of microseconds to sleep for
export
usleep : HasIO io => (usec : Int) -> So (usec >= 0) => io ()
usleep usec = primIO (prim__usleep usec)

-- Get the number of arguments
-- Note: node prefixes the list of command line arguments
--       with the path to the `node` executable. This is
--       inconsistent with other backends, which only list
--       the path to the running program. For reasons of
--       consistency across backends, this first argument ist
--       dropped on the node backend.
%foreign "scheme:blodwen-arg-count"
         supportC "idris2_getArgCount"
         "node:lambda:() => process.argv.length - 1"
prim__getArgCount : PrimIO Int

-- Get argument number `n`. See also `prim__getArgCount`
-- about the special treatment of the node backend.
%foreign "scheme:blodwen-arg"
         supportC "idris2_getArg"
         "node:lambda:n => process.argv[n + 1]"
prim__getArg : Int -> PrimIO String

||| Retrieve the arguments to the program call, if there were any.
export
getArgs : HasIO io => io (List String)
getArgs = do
            n <- primIO prim__getArgCount
            if n > 0
              then for [0..n-1] $ primIO . prim__getArg
              else pure []

%foreign libc "getenv"
         "node:lambda: n => process.env[n]"
prim__getEnv : String -> PrimIO (Ptr String)

%foreign supportC "idris2_getEnvPair"
prim__getEnvPair : Int -> PrimIO (Ptr String)
%foreign supportC "idris2_setenv"
         supportNode "setEnv"
prim__setEnv : String -> String -> Int -> PrimIO Int
%foreign supportC "idris2_unsetenv"
         supportNode "unsetEnv"
prim__unsetEnv : String -> PrimIO Int

||| Retrieve the specified environment variable's value string, or `Nothing` if
||| there is no such environment variable.
|||
||| @ var the name of the environment variable to look up
export
getEnv : HasIO io => (var : String) -> io (Maybe String)
getEnv var
   = do env <- primIO $ prim__getEnv var
        if prim__nullPtr env /= 0
           then pure Nothing
           else pure (Just (prim__getString env))

||| Retrieve all the key-value pairs of the environment variables, and return a
||| list containing them.
export
covering
getEnvironment : HasIO io => io (List (String, String))
getEnvironment = getAllPairs 0 []
  where
    splitEq : String -> (String, String)
    splitEq str
        = let (k, v)  = break (== '=') str
              (_, v') = break (/= '=') v in
              (k, v')

    getAllPairs : Int -> List String -> io (List (String, String))
    getAllPairs n acc = do
      envPair <- primIO $ prim__getEnvPair n
      if prim__nullPtr envPair /= 0
         then pure $ reverse $ map splitEq acc
         else getAllPairs (n + 1) (prim__getString envPair :: acc)

||| Add the specified variable with the given value string to the environment,
||| optionally overwriting any existing environment variable with the same name.
||| Returns True whether the value is set, overwritten, or not overwritten because
||| overwrite was False. Returns False if a system error occurred. You can `getErrno`
||| to check the error.
|||
||| @ var       the name of the environment variable to set
||| @ val       the value string to set the environment variable to
||| @ overwrite whether to overwrite the existing value if an environment
|||             variable with the specified name already exists
export
setEnv : HasIO io => (var : String) -> (val : String) -> (overwrite : Bool) ->
                     io Bool
setEnv var val overwrite
   = do ok <- primIO $ prim__setEnv var val (if overwrite then 1 else 0)
        pure $ ok == 0

||| Delete the specified environment variable. Returns `True` either if the
||| value was deleted or if the value was not defined/didn't exist. Returns
||| `False` if a system error occurred. You can `getErrno` to check the error.
export
unsetEnv : HasIO io => (var : String) -> io Bool
unsetEnv var
   = do ok <- primIO $ prim__unsetEnv var
        pure $ ok == 0

%foreign "C:idris2_system, libidris2_support, idris_system.h"
         supportNode "spawnSync"
prim__system : String -> PrimIO Int

||| Execute a shell command, returning its termination status or -1 if an error
||| occurred.
export
system : HasIO io => String -> io Int
system cmd = primIO (prim__system cmd)

namespace Escaped
  export
  system : HasIO io => List String -> io Int
  system = system . escapeCmd

||| Run a shell command, returning its stdout, and exit code.
export
covering
run : HasIO io => (cmd : String) -> io (String, Int)
run cmd = do
    Right f <- popen cmd Read
        | Left err => pure ("", 1)
    Right resp <- fRead f
        | Left err => pure ("", 1)
    exitCode <- pclose f
    pure (resp, exitCode)

namespace Escaped
  export
  covering
  run : HasIO io => (cmd : List String) -> io (String, Int)
  run = run . escapeCmd

||| Run a shell command, allowing processing its stdout line by line.
|||
||| Notice that is the line of the command ends with a newline character,
||| it will be present in the string passed to the processing function.
|||
||| This function returns an exit code which value should be consistent with the `run` function.
export
covering
runProcessingOutput : HasIO io => (String -> io ()) -> (cmd : String) -> io Int
runProcessingOutput pr cmd = do
  Right f <- popen cmd Read
    | Left err => pure 1
  True <- process f
    | False => pure 1 -- we do not close `f` in case of reading error, like `run` does
  pclose f

  where
    process : File -> io Bool
    process h = if !(fEOF h) then pure True else do
      Right line <- fGetLine h
        | Left err => pure False
      pr line
      process h

namespace Escaped
  export
  covering
  runProcessingOutput : HasIO io => (String -> io ()) -> (cmd : List String) -> io Int
  runProcessingOutput pr = runProcessingOutput pr . escapeCmd

%foreign supportC "idris2_time"
         "javascript:lambda:() => Math.floor(new Date().getTime() / 1000)"
prim__time : PrimIO Int

||| Return the number of seconds since epoch.
export
time : HasIO io => io Integer
time = pure $ cast !(primIO prim__time)

%foreign supportC "idris2_getPID"
         "node:lambda:() => process.pid"
prim__getPID : PrimIO Int

||| Get the ID of the currently running process.
export
getPID : HasIO io => io Int
getPID = primIO prim__getPID

%foreign libc "exit"
         "node:lambda:c => process.exit(c)"
prim__exit : Int -> PrimIO ()

||| Programs can either terminate successfully, or end in a caught
||| failure.
public export
data ExitCode : Type where
  ||| Terminate successfully.
  ExitSuccess : ExitCode
  ||| Program terminated for some prescribed reason.
  |||
  ||| @errNo A non-zero numerical value indicating failure.
  ||| @prf   Proof that the int value is non-zero.
  ExitFailure : (errNo    : Int) -> (So (not $ errNo == 0)) => ExitCode

||| Exit the program normally, with the specified status.
export
exitWith : HasIO io => ExitCode -> io a
exitWith ExitSuccess = primIO $ believe_me $ prim__exit 0
exitWith (ExitFailure code) = primIO $ believe_me $ prim__exit code

||| Exit the program with status value 1, indicating failure.
||| If you want to specify a custom status value, see `exitWith`.
export
exitFailure : HasIO io => io a
exitFailure = exitWith (ExitFailure 1)

||| Exit the program after a successful run.
export
exitSuccess : HasIO io => io a
exitSuccess = exitWith ExitSuccess

||| Print the error message and call exitFailure
export
die : HasIO io => String -> io a
die str
  = do ignore $ fPutStrLn stderr str
       exitFailure
