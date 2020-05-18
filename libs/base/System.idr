module System

import Data.So
import Data.List
import Data.Strings

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

libc : String -> String
libc fn = "C:" ++ fn ++ ", libc 6"

%foreign support "idris2_sleep"
prim_sleep : Int -> PrimIO ()
%foreign support "idris2_usleep"
prim_usleep : Int -> PrimIO ()

export
sleep : Int -> IO ()
sleep sec = primIO (prim_sleep sec)

export
usleep : (x : Int) -> So (x >= 0) => IO ()
usleep sec = primIO (prim_usleep sec)

-- This one is going to vary for different back ends. Probably needs a
-- better convention. Will revisit...
%foreign "scheme:blodwen-args"
prim__getArgs : PrimIO (List String)

export
getArgs : IO (List String)
getArgs = primIO prim__getArgs

%foreign libc "getenv"
prim_getEnv : String -> PrimIO (Ptr String)
%foreign support "idris2_getEnvPair"
prim_getEnvPair : Int -> PrimIO (Ptr String)
%foreign libc "setenv"
prim_setEnv : String -> String -> Int -> PrimIO Int
%foreign libc "setenv"
prim_unsetEnv : String -> PrimIO Int

export
getEnv : String -> IO (Maybe String)
getEnv var
   = do env <- primIO $ prim_getEnv var
        if prim__nullPtr env /= 0
           then pure Nothing
           else pure (Just (prim__getString env))

export
getEnvironment : IO (List (String, String))
getEnvironment = getAllPairs 0 []
  where
    splitEq : String -> (String, String)
    splitEq str
        = let (k, v)  = break (== '=') str
              (_, v') = break (/= '=') v in
              (k, v')

    getAllPairs : Int -> List String -> IO (List (String, String))
    getAllPairs n acc = do
      envPair <- primIO $ prim_getEnvPair n
      if prim__nullPtr envPair /= 0
         then pure $ reverse $ map splitEq acc
         else getAllPairs (n + 1) (prim__getString envPair :: acc)

export
setEnv : String -> String -> Bool -> IO Bool
setEnv var val overwrite
   = do ok <- primIO $ prim_setEnv var val (if overwrite then 1 else 0)
        if ok == 0
           then pure True
           else pure False

export
unsetEnv : String -> IO Bool
unsetEnv var
   = do ok <- primIO $ prim_unsetEnv var
        if ok == 0
           then pure True
           else pure False

%foreign libc "system"
         "scheme:blodwen-system"
prim_system : String -> PrimIO Int

export
system : String -> IO Int
system cmd = primIO (prim_system cmd)

%foreign support "idris2_time"
         "scheme:blodwen-time"
prim_time : PrimIO Int

export
time : IO Integer
time = pure $ cast !(primIO prim_time)

%foreign libc "exit"
prim_exit : Int -> PrimIO ()

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

export
exitWith : ExitCode -> IO a
exitWith ExitSuccess = believe_me $ primIO $ prim_exit 0
exitWith (ExitFailure code) = believe_me $ primIO $ prim_exit code

||| Exit the program indicating failure.
export
exitFailure : IO a
exitFailure = exitWith (ExitFailure 1)

||| Exit the program after a successful run.
export
exitSuccess : IO a
exitSuccess = exitWith ExitSuccess
