import System.File

main : IO ()
main = do
    putStrLn "main thread: before all"
    Right process <- popen2 "cat"
        | Left err => printLn err
    printLn $ process.pid > 0
    _ <- fPutStrLn process.input "Hello, Idris!\n"
    putStrLn "main thread: before closing subinput"
    closeFile process.input
    putStrLn "main thread: before reading suboutput"
    Right result <- fRead process.output
        | Left err => printLn err
    putStrLn "main thread: before printing suboutput"
    putStr result
    putStrLn "main thread: after all"
