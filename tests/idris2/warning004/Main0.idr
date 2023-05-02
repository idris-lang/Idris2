module Main

import Lib1
import Lib2

main : IO ()
main = printLn (10 %%% 10 %%% 1)
