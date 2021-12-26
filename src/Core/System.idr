module Core.System

--import Core.Context
--import Core.Context.Log
import Core.Core
--import Core.FC
--import Core.Options
--import Libraries.Utils.Path

--import Data.List
--import Data.Maybe

import System
import System.File.Permissions

%default total

export
system_ : String -> Core ()
system_ cmd = do
  n <- coreLift $ system cmd
  if n == -1
     then throw $ InternalError $ cmd ++ ": failed with exit code " ++ show n
     else pure ()

export
chmodRaw_ : String -> Int -> Core ()
chmodRaw_ fname p = do
  Right () <- coreLift $ chmodRaw fname p
       | Left err => throw (FileErr fname err)
  pure ()

