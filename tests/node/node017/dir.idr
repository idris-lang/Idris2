import System.Directory

main : IO ()
main = do Right () <- createDir "testdir"
               | Left err => printLn err
          Left err <- createDir "testdir"
               | _ => printLn "That wasn't supposed to work"
          printLn err
          ok <- changeDir "nosuchdir"
          printLn ok
          ok <- changeDir "testdir"
          printLn ok
          writeFile "test.txt" "hello\n"
          printLn !currentDir

