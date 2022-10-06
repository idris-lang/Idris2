import System
import System.File

main : IO ()
main = do
  Right () <- writeFile "hello.txt" "hello"
    | _ => die "Failed to create file during test setup"
  True <- exists "hello.txt"
    | _ => die "assumption that written file exists did not hold."
  Right () <- removeFile "hello.txt"
    | _ => die "Failed to remove file"
  case !(exists "hello.txt") of
       True => die "Supposedly removed file still exists."
       False => putStrLn "Good deal!"
