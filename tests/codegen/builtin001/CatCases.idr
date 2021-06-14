import System.File

main : IO ()
main = do
    Right str <- readFile "Main.cases"
        | Left err => putStrLn "Error:" *> printLn err
    putStrLn str
