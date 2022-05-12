import Data.Vect

takeFromStream : List (n ** Vect n Int)
takeFromStream = [(n ** take n [3..]) | n <- [0, 1, 5]]

scanrMul = List (n ** Vect n Nat)
scanrMul = [
      scanr (*) 1 []
    , scanr (*) 1 [4]
    , scanr (*) 1 [2, 3, 4]
  ]

scanrCons : Vect 4 (List Nat)
scanrCons = scanr (::) Nil [2, 3, 4]

main : IO ()
main = do
  printLn takeFromStream
  printLn scanrMul
  printLn scanrCons
