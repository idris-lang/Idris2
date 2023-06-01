import System.File
foo : File -> IO ()
foo file = do
    stuff <- fgetLine file
    case stuff of
      (Left err) => printLn err
      (Right content) => if content == ""
                            then println "Empty"
                            else blah <- doSomething
                                 putStrLn content
