import System.File

total
totalChecks : IO ()
totalChecks =
  do Right (False, l1) <- readFilePage 0 (lineCount 0) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putStrLn $ "empty: " ++ (show l1)
     Right (False, l2) <- readFilePage 0 (lineCount 1) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putStrLn l2
     Right (False, l3) <- readFilePage 1 (lineCount 2) "test.txt"
       | Right (True, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putStrLn l3
     Right (True, l4) <- readFilePage 0 (lineCount 100) "test.txt"
       | Right (False, _) => putStrLn "Failed EOF check"
       | Left err => putStrLn $ show err
     putStrLn l4

partial
main : IO ()
main = do totalChecks
          Right (True, l5) <- readFilePage 0 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putStrLn l5
          Right (True, l6) <- readFilePage 2 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putStrLn l6
          Right (True, l7) <- readFilePage 100 forever "test.txt"
            | Right (False, _) => putStrLn "Failed EOF check"
            | Left err => putStrLn $ show err
          putStrLn $ "empty: " ++ (show l7)
