import Data.String

import System
import System.Info

main : IO ()
main = do
    (contents, 0) <- run $ "echo " ++ escapeArg "Hello, world"
        | (_, err) => printLn err
    printLn $ trim contents

    let cmd : List String = if not isWindows
                               then ["printf", "Hello, %s", "$PATH"]
                               else ["echo", "Hello, $PATH"]
    (contents, 0) <- run cmd
        | (_, err) => printLn err
    printLn $ trim contents

    printLn !(run ["exit", "17"])
