import System

main : IO ()
main = do
  env <- getEnvironment
  -- it better be non-empty because we set a variable before starting this test
  printLn $ null env

