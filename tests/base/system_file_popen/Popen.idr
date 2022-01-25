import Data.String

import System.File
import System.Info

main : IO ()
main = do
    Right f <- popen ("echo " ++ escapeArg "Hello, world") Read
        | Left err => printLn err
    Right contents <- fGetLine f
        | Left err => printLn err
    printLn $ trim contents
    0 <- pclose f
        | n => printLn n

    let cmd : List String = if not isWindows
                               then ["printf", "Hello, %s", "$PATH"]
                               else ["echo", "Hello, $PATH"]
    Right f <- popen cmd Read
        | Left err => printLn err
    Right contents <- fGetLine f
        | Left err => printLn err
    printLn $ (ifThenElse isWindows trim id) contents
    0 <- pclose f
        | n => printLn n

    Right f <- popen ["exit", "17"] Read
        | Left err => printLn err
    printLn !(pclose f)
