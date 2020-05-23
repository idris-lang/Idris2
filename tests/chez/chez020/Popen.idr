import System
import System.File
import Data.Strings

main : IO ()
main = do
    Just cmd <- getEnv "POPEN_CMD"
        | Nothing => putStrLn "POPEN_CMD env var not set"
    Right fh <- popen cmd Read
        | Left err => printLn err
    putStrLn "opened"
    Right output <- fGetLine fh
        | Left err => printLn err
    pclose fh
    putStrLn "closed"
    let [idris2, _] = split ((==) ',') output
        | _ => printLn "Unexpected result"
    putStrLn idris2
