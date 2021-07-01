main : IO ()
main = do
  printLn $ the Nat $ fromInteger (-1)
  printLn $ the Nat $ fromInteger 1000000000
