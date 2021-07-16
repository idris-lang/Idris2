import System
import System.Directory

panic : String -> IO a
panic s = do putStrLn s
             exitFailure

collectEntries : Directory -> IO (List String)
collectEntries d = do Right (Just n) <- nextDirEntry d
                        | Right Nothing => pure []
                        | Left e        => panic (show e)
                      ns <- collectEntries d
                      pure (n :: ns)

main : IO ()
main = do Right d <- openDir "dir"
            | Left e => panic (show e)
          ["a"] <- collectEntries d
            | x => panic ("wrong entries: " ++ (show x))
          pure ()
