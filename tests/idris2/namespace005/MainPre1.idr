module Main

import Lib1
import LibPre1
import LibPre2

%hide LibPre1.prefix.(*!)

main : IO ()
main = printLn (*! 10 %%% 10) -- should be 0
