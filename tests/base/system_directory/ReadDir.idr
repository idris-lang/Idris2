import System
import System.Directory

panic : String -> IO a
panic s = do putStrLn s
             exitFailure

main : IO ()
main = do Right ["a"] <- listDir "dir"
            | Left e => panic (show e)
            | Right x => panic ("wrong entries: " ++ (show x))
          pure ()
