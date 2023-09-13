module Main

import Lib2
import Lib1

%hide Lib2.infixl.(%%%)

main : IO ()
main = printLn (10 %%% 10 %%% 1)
