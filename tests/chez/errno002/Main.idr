import System.Directory

go : String -> Integer -> IO (Maybe FileError)
go pref n
  = if n == 0
       then pure Nothing
       else do let dir = pref ++ show n
               Right _ <- createDir dir
                 | Left err => pure $ Just err
               Right _ <- listDir dir
                 | Left err => pure $ Just err
               removeDir dir
               go pref (n - 1)

main : IO ()
main = printLn =<< go "dir" 100000
