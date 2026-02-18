import System

main : IO ()
main = do
  printLn !(getEnv "HELLO")
  True <- setEnv "WORLD" "world" False
    | _ => putStrLn "Failed to set ENV 1"
  printLn !(getEnv "WORLD")
  True <- setEnv "WORLD" "other world" False
    | _ => putStrLn "Failed to set ENV 2"
  -- ^ should not overwrite
  printLn !(getEnv "WORLD")
  True <- setEnv "WORLD" "third rock from sun" True
    | _ => putStrLn "Failed to set ENV 3"
  printLn !(getEnv "WORLD")

  printLn !(getEnv "UNSET")
