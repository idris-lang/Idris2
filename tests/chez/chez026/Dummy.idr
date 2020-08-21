module Dummy

import System.Directory

dirExists : String -> IO Bool
dirExists dir = do
  Right d <- openDir dir
    | Left _ => pure False
  closeDir d
  pure True

main : IO ()
main = do
  True <- dirExists "custom_build"
    | False => putStrLn "Could not find build directory"
  putStrLn "Found build directory"
