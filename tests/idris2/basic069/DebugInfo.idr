main : IO ()
main = do

  putStrLn "loc: \{__LOC__}"

  putStrLn "file: \{__FILE__}"

  putStrLn "line: \{__LINE__}"

  putStrLn "col:      \{__COL__}"

  putStrLn
      """
      loc further down the file: \{



           __LOC__}
      """

  putStrLn __FILE__
