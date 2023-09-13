%foreign "scheme,racket:(lambda (x) (if (port-number? x) 1 0)),racket/tcp"
isPortNumber : Int -> Bool

main : IO ()
main = do
  putStrLn $ "0 is port: " ++ show (isPortNumber 0)
  putStrLn $ "1 is port: " ++ show (isPortNumber 1)
  putStrLn $ "2 is port: " ++ show (isPortNumber 2)
