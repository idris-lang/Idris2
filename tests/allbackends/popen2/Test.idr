import System.File

main : IO ()
main = do
    Right process <- popen2 "cat"
        | Left err => printLn err
    printLn $ process.pid > 0
    _ <- fPutStrLn process.input "Hello, Idris!\n"
    closeFile process.input
    Right result <- fRead process.output
        | Left err => printLn err
    putStr result
