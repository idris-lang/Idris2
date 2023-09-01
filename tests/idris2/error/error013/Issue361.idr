%default total

data S = T | F

Eq S where

main : IO ()
main = printLn $ T == T

%default covering
