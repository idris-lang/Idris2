module Tail

import Data.String

main : IO ()
main = assert_total $ do
  putStrLn $ strTail ""
  putStrLn $ strTail " Hello World!"
