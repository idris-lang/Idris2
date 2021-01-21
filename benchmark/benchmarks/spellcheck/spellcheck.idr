import System.File
import Data.Strings
import Data.List

main : IO ()
main = do
    putStrLn "input file: "
    file<-getLine
    Right tocheck<-readFile file
     | Left err => putStrLn $show err
    Right dict<-readFile "words"
     | Left err => putStrLn $show err
    let diff = filter (\s=>not $ s `elem` words dict) $ words tocheck
    putStrLn $ show diff
