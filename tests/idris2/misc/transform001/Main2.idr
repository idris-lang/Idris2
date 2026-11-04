module Main

import B
import A

-- The named module loads first: the rule has always fired here.
main : IO ()
main = printLn (foo 1)
