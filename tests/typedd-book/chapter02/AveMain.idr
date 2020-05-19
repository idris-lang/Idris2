module Main

import System.REPL
import Average

showAverage : String -> String
showAverage str = "The average word length is: " ++
                  show (average str) ++ "\n"

main : IO ()
main = repl "Enter a string: " showAverage
