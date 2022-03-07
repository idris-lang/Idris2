module Main

import System.File
import Data.String
import Data.List1
import Data.List

parse : String -> Maybe String
parse x = case forget $ split (\c => c == ' ' || c == '(')  x of
    "function" :: name :: _ => Just name
    _ => Nothing

main : IO ()
main = do
    Right res <- readFile "build/exec/app.js" | Left err => printLn err
    let fns = mapMaybe parse $ lines res
    printLn $ fns \\ nub fns
