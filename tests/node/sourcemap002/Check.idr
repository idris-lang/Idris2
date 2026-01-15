module Main

import Data.String
import System.File

contains : String -> String -> Bool
contains haystack needle = isInfixOf needle haystack

-- Check that generated JS has no shebang (browser-compatible)
checkNoShebang : String -> Bool
checkNoShebang content = not (isPrefixOf "#!" content)

verifySourceMap : String -> IO ()
verifySourceMap content = do
  putStrLn $ "Has version 3: " ++ show (contains content "\"version\":3")
  putStrLn $ "Has sources: " ++ show (contains content "\"sources\"")
  putStrLn $ "Has mappings: " ++ show (contains content "\"mappings\"")

main : IO ()
main = do
  putStrLn "--- JavaScript backend source map test ---"
  -- Check JS file has no shebang (javascript backend outputs without .js extension)
  Right jsContent <- readFile "build/exec/browser_app"
    | Left err => putStrLn $ "Error reading JS file: " ++ show err
  putStrLn $ "No shebang (browser-compatible): " ++ show (checkNoShebang jsContent)
  -- Check source map
  Right mapContent <- readFile "build/exec/browser_app.map"
    | Left err => putStrLn $ "Error reading map file: " ++ show err
  verifySourceMap mapContent
