import Data.Vect

takeFromStream : List (n ** Vect n Int)
takeFromStream = [(n ** take n [3..]) | n <- [0, 1, 5]]

main : IO ()
main = do printLn takeFromStream
