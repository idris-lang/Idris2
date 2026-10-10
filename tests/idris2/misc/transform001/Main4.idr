module Main

import A
import A2
import B

-- A rule declared here is tried before any imported one.
%transform "localRule" B.foo n = 200

main : IO ()
main = printLn (foo 1)
