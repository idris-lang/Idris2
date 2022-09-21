import System.File

main : IO ()
main = do
    Right f <- openFile "sampleFile.txt" Read
        | Left err => printLn err
    Right contents <- fRead f
        | Left err => printLn err
    printLn contents
