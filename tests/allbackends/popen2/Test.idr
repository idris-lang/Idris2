import System.File

runPopen2 : (cmd : String) -> IO ()
runPopen2 cmd = do
    putStrLn "main thread: before all"
    Right process <- popen2 cmd
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
    putStrLn "main thread: before waiting subprocess"
    exitCode <- popen2Wait process
    putStrLn "subprocess exit code: \{show exitCode}"
    putStrLn "main thread: after all"

main : IO ()
main = runPopen2 "cat"

main2 : IO ()
main2 = runPopen2 "cat && exit 4"

main3 : IO ()
main3 = runPopen2 "cat && echo \"Two  spaces\" && exit 4"
