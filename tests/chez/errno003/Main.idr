import System.Directory

go : String -> Integer -> List String -> IO (Maybe FileError)
go pref n dirs
  = if n == 0
       then do
        for_ dirs $ \d => removeDir d
        pure Nothing
       else do let dir = pref ++ show n
               Right _ <- createDir dir
                 | Left err => pure $ Just err
               Right _ <- listDir dir
                 | Left err => pure $ Just err
               go pref (n - 1) (dir :: dirs)

main : IO ()
main = do
  printLn =<< go "dir" 100000 []
