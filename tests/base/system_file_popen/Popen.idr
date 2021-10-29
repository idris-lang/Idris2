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

    let cmd : List String = if not isWindows
                               then ["printf", "Hello, %s", "$PATH"]
                               else ["echo", "Hello, $PATH"]
    Right f <- popen cmd Read
        | Left err => printLn err
    Right contents <- fGetLine f
        | Left err => printLn err
    printLn $ (ifThenElse isWindows trim id) contents
