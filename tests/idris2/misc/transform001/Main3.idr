module Main

import A
import A2
import B

-- Two imported rules for one function: the one loaded last is tried first.
main : IO ()
main = printLn (foo 1)
