module Main

import Lib2
import Lib1

main : IO ()
main = printLn (10 %%% 10 %%% 1)
