import System.File
import Data.String

putLines : List String -> IO ()
putLines = putStrLn . fastConcat

total
totalChecks : IO ()
totalChecks =
  do Right (False, l1) <- readFilePage 0 (limit 0) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putStrLn $ "empty: " ++ (show l1)
     Right (False, l2) <- readFilePage 0 (limit 1) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putLines l2
     Right (False, l3) <- readFilePage 1 (limit 2) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putLines l3
     Right (True, l4) <- readFilePage 0 (limit 100) "test.txt"
       | Right (False, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putLines l4

partial
main : IO ()
main = do totalChecks
          Right (True, l5) <- readFilePage 0 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putLines l5
          Right (True, l6) <- readFilePage 2 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putLines l6
          Right (True, l7) <- readFilePage 100 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putStrLn $ "empty: " ++ (show l7)
          Right l8 <- readFile "test.txt"
            | Left err => putStrLn $ show err
          putStrLn l8
