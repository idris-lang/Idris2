module Main

import Libraries.Data.Version
import PrimIO

parseAndShow : Version -> Maybe String
parseAndShow =  map (showVersion True) . parseVersion . showVersion True

main : IO ()
main = do
  printLn $ parseAndShow $ MkVersion (1,2,3) Nothing
  printLn $ parseAndShow $ MkVersion (1,2,3) (Just "bar")
  printLn $ parseAndShow $ MkVersion (10,200,3) (Just "foo")
  printLn $ map (showVersion True) $ parseVersion "1.2.3-  foo"
  printLn $ map (showVersion True) $ parseVersion "1.2"
  printLn $ map (showVersion True) $ parseVersion "1.2."
  printLn $ map (showVersion True) $ parseVersion "1.2.3."
