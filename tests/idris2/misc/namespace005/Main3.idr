module Main3

import Lib1

private prefix 4 %%%
private infixr 8 -

(%%%) : Nat -> Nat
(%%%) = S

main : IO ()
main = do printLn (the Nat (%%% 4))
          printLn (1 - 1 - 1)
