import Data.Vect

testTakeFromStream : List (n ** Vect n Int)
testTakeFromStream = [n ** take n [3..] | n <- [0, 1, 5]]

main : IO ()
main = do printLn testTakeFromStream
