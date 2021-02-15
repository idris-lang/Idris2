-- import System.File

main : IO ()
main = do -- l1 <- readFilePage 0 0 "test.txt"
          let l1 = "hello world"
          putStrLn $ "emty: " ++ (show l1)
--           l2 <- readFilePage 0 1 "test.txt"
--           putStrLn l2
