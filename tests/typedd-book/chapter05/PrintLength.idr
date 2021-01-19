printLength : IO ()
printLength = putStr "Input string: " >>= \_ =>
              getLine >>= \input =>
              let len = length input in
              putStrLn (show len)
