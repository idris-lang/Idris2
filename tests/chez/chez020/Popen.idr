import System
import System.File
import System.Info
import Data.List1
import Data.Strings

windowsPath : String -> String
windowsPath path =
    let replaceSlashes : List Char -> List Char
        replaceSlashes [] = []
        replaceSlashes ('/' :: cs) = '\\' :: replaceSlashes cs
        replaceSlashes (c :: cs) = c :: replaceSlashes cs
    in
        pack $ replaceSlashes (unpack path)

main : IO ()
main = do
    Just cmd <- getEnv "POPEN_CMD"
        | Nothing => putStrLn "POPEN_CMD env var not set"
    let cmd = if isWindows then windowsPath cmd else cmd
    Right fh <- popen cmd Read
        | Left err => printLn err
    putStrLn "opened"
    Right output <- fGetLine fh
        | Left err => printLn err
    pclose fh
    putStrLn "closed"
    let (idris2 ::: _) = split ((==) ',') output
        | _ => printLn "Unexpected result"
    putStrLn idris2
