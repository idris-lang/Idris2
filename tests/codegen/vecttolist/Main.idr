import Data.Vect

xs : Vect 3 Int
xs = [1, 2, 3]

main : IO ()
main = printLn $ toList xs
