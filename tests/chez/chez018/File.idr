import System.File

main : IO ()
main
    = do Right ok <- readFile "test.txt"
               | Left err => printLn err
         putStr ok
         ignore $ writeFile "testout.txt" "abc\ndef\n"
         Right ok <- readFile "testout.txt"
               | Left err => printLn err
         putStr ok
         Right ok <- readFile "notfound"
               | Left err => printLn err
         putStr ok
