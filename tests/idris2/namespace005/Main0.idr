module Main

import Lib1
import Lib2

%hide Lib1.infixr.(%%%)

main : IO ()
main = printLn (10 %%% 10 %%% 1)
