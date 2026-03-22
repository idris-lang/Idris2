module Main

import Data.String
import System.File

-- Simple test functions to generate some code
add : Int -> Int -> Int
add x y = x + y

-- Check if a string contains a substring
contains : String -> String -> Bool
contains haystack needle = isInfixOf needle haystack

-- Verify source map file
verifySourceMap : String -> IO ()
verifySourceMap content = do
  putStrLn $ "Has version 3: " ++ show (contains content "\"version\":3")
  putStrLn $ "Has sources: " ++ show (contains content "\"sources\"")
  putStrLn $ "Has mappings: " ++ show (contains content "\"mappings\"")

main : IO ()
main = do
  putStrLn "--- Program output ---"
  putStrLn "Source map test"
  printLn (add 1 2)
  putStrLn "--- Source map verification ---"
  Right content <- readFile "build/exec/sourcemap_test.map"
    | Left err => putStrLn $ "Error reading map file: " ++ show err
  verifySourceMap content
