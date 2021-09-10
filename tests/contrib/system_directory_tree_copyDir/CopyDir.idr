import System.Directory.Tree
import System.File
import System.Path

main : IO ()
main = do
    Right () <- copyDir (parse "templateDir") (parse "resultDir")
        | Left err => printLn err
    pure ()
