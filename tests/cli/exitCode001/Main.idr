module Main

import System

success : IO ()
success = putStrLn "Success"

fail : IO ()
fail = do
  putStrLn "Fail"
  exitWith (ExitFailure 42)
