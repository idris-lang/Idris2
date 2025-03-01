import System.File
import System.Directory

main : IO ()
main = do
  Left FileNotFound <- openFile "doesNotExist" Read
    | Right _ => putStrLn "expected FileNotFound error"
    | Left err => putStrLn "expected FileNotFound, got \{show err}"

  Left PermissionDenied <- openFile "read_only.txt" ReadWrite
    | Right _ => putStrLn "expected PermissionDenied error"
    | Left err => putStrLn "expected PermissionDenied, got \{show err}"

  Left FileExists <- createDir "build"
    | Right _ => putStrLn "expected FileExists error"
    | Left err => putStrLn "expected FileExists, got \{show err}"

  putStrLn "done"
