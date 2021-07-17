import Data.String

main : IO ()
main = do printLn (lines "")
          printLn (lines "ab")
          printLn (lines "ab\n")
          printLn (lines "ab\ncd")
          printLn (lines "ab\ncd\n")
          printLn (lines "a\rb")
          printLn (lines "a\r\nb")
          printLn (lines "\n\r\n\n")
