module Libraries.System

import Data.String

import System
import System.Info
import System.File
import Libraries.System.File.ReadWrite as Lib

||| Run a shell command, returning its stdout, and exit code.
export
covering
run : HasIO io => (cmd : String) -> io (String, Int)
run cmd = do
    Right f <- popen cmd Read
        | Left err => pure ("", 1)
    Right resp <- Lib.fRead f
        | Left err => pure ("", 1)
    _ <- pclose f -- previous version does not return an exit code
                  -- so assuming this succeeded, for now
    pure (resp, 0)

||| Locate a command, returning its absolute path if it was found
export covering
which : HasIO io => (cmd : String) -> io (Maybe String)
which cmd = do
  let which = ifThenElse isWindows "where.exe" "which"
  (cmd, i) <- Libraries.System.run #"\#{which} "\#{cmd}""#
  pure $ do guard (i == 0)
            let [cmd] = lines cmd
              | _ => Nothing
            pure cmd
