module System.File.Permissions

import public System.File.Error
import System.File.Meta
import System.File.Support
import public System.File.Types

%default total

%foreign support "idris2_chmod"
         "node:support:chmod,support_system_file"
prim__chmod : String -> Int -> PrimIO Int

namespace FileMode
  public export
  data FileMode = Read | Write | Execute

public export
record Permissions where
  constructor MkPermissions
  user   : List FileMode
  group  : List FileMode
  others : List FileMode

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

export
chmodRaw : HasIO io => String -> Int -> io (Either FileError ())
chmodRaw fname p
    = do ok <- primIO $ prim__chmod fname p
         if ok == 0
            then pure (Right ())
            else returnError

export
chmod : HasIO io => String -> Permissions -> io (Either FileError ())
chmod fname p = chmodRaw fname (mkMode p)
