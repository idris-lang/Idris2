import System.File

read10 : String -> IO ()
read10 fileName = do
    Right f <- openFile fileName Read
        | Left err => printLn err
    Right contents <- fGetChars f 10
        | Left err => printLn err
    printLn contents

main : IO ()
main = do
  read10 "small.txt"
  read10 "big.txt"
  read10 "empty.txt"
