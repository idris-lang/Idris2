import System
import System.Errno

main : IO ()
main = do
  -- `2` is `ENOENT` on all OS
  -- and the message is the same on all OS
  let s = strerror 2
  True <- pure (s == "No such file or directory")
    | False => do
      putStrLn ("strerror for 2 is " ++ s)
      exitFailure
  pure ()
