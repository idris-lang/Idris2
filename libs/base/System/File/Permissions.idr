module System.File.Permissions

import public System.File.Error
import System.File.Support
import public System.File.Types

%default total

%foreign supportC "idris2_chmod"
         supportNode "chmod"
prim__chmod : String -> Int -> PrimIO Int

||| The UNIX file modes.
namespace FileMode
  public export
  data FileMode = Read | Write | Execute

||| The permissions of a file, grouped by the 3 types of owners of a file.
public export
record Permissions where
  constructor MkPermissions
  user   : List FileMode
  group  : List FileMode
  others : List FileMode

||| Convert the given `Permissions` to their integer value.
mkMode : Permissions -> Int
mkMode p
    = getMs (user p) * 64 + getMs (group p) * 8 + getMs (others p)
  where
    getM : FileMode -> Int
    getM Read = 4
    getM Write = 2
    getM Execute = 1

    getMs : List FileMode -> Int
    getMs = sum . map getM

||| Change the permissions of the file with the specified name to the given
||| integer representation of some permissions.
||| You likely want to use `chmod` and `Permissions`, or go via `mkMode`
||| instead of using this.
|||
||| @ fname the name of the file whose permissions to change
||| @ p     the integer representation of the permissions to set
export
chmodRaw : HasIO io => (fname : String) -> (p : Int) -> io (Either FileError ())
chmodRaw fname p
    = do ok <- primIO $ prim__chmod fname p
         if ok == 0
            then pure (Right ())
            else returnError

||| Change the permissions of the file with the specified name to the
||| permissions in the given `Permissions` record.
|||
||| @ fname the name of the file whose permissions to change
||| @ p     a `Permissions` record containing the permissions to set
export
chmod : HasIO io => (fname : String) -> (p : Permissions) -> io (Either FileError ())
chmod fname p = chmodRaw fname (mkMode p)
