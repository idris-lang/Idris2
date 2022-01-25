||| Tests that no duplication occurs in recursive calls
||| as fixed in #1494
import Data.List

ints : List Int
ints = [1..100]

main : IO ()
main = printLn $ span (80 >=) ints
