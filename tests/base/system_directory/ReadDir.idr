import System
import System.Directory

panic : String -> IO a
panic s = do putStrLn s
             exitFailure

main : IO ()
main = do -- Verify that errorno does not cause subsequent listDir to fail
          Left _ <- listDir "doesNotExist"
            | Right _ => panic "Read of \"doesNotExist\" succeeded"
          Right ["a"] <- listDir "dir"
            | Left e => panic (show e)
            | Right x => panic ("wrong entries: " ++ (show x))
          pure ()
