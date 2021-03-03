module Tail

import Data.Strings

main : IO ()
main = assert_total $ do
  putStrLn $ strTail ""
  putStrLn $ strTail " Hello World!"
