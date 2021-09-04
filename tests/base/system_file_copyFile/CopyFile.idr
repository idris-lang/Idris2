import System.File

main : IO ()
main = do
    Right () <- copyFile "source.bin" "dest.bin"
        | Left err => printLn err
    pure ()
