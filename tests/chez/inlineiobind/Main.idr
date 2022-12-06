main : IO ()
main = do
  putStrLn "What is your name?"
  nm <- getLine
  putStrLn "Hello \{nm}"
