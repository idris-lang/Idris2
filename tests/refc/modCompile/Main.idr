module Main

import Lib

main : IO ()
main = do
    putStrLn (greet "world")
    printLn (add 3 4)
