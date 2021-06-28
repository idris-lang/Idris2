import System
import System.Info

main : IO ()
main = do
  Just expectedOs <- getEnv "EXPECTED_OS"
    | Nothing => do
      putStrLn "EXPECTED_OS unset"
      exitFailure
  case os == expectedOs of
    True => putStrLn "correct"
    False => do
      putStrLn ("os=" ++ os ++ " expected=" ++ expectedOs)
      exitFailure
