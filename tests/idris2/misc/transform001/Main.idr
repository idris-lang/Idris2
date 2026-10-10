module Main

import A
import B

-- The rule's module loads before the module it names.
main : IO ()
main = printLn (foo 1)
