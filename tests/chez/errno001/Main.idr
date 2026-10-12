import System.Directory

go : String -> Integer -> IO (Maybe FileError)
go dir n
  = if n == 0
       then pure Nothing
       else do Right _ <- listDir dir
                 | Left err => pure $ Just err
               go dir (n - 1)

main : IO ()
main = printLn =<< go "dir" 100000
