module Main

import Lib1
import LibPre1
import LibPre2

%hide LibPre2.prefix.(*!)

main : IO ()
main = printLn (*! 10 %%% 10) -- should be 90
