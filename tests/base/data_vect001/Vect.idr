import Data.Vect

takeFromStream : List (n ** Vect n Int)
takeFromStream = [(n ** take n [3..]) | n <- [0, 1, 5]]

scanrMul = List (n ** Vect n Nat)
scanrMul = [
      scanr (*) 2 []
    , scanr (*) 2 [3]
    , scanr (*) 2 [5, 4, 3]
  ]

scanrCons : Vect 4 (List Nat)
scanrCons = scanr (::) Nil [2, 3, 4]

scanr1Mul = List (n ** Vect n Nat)
scanr1Mul = [
      scanr (*) [3]
    , scanr (*) [5, 4, 3]
  ]

main : IO ()
main = do
  printLn takeFromStream
  printLn scanrMul
  printLn scanrCons
  printLn scanr1Mul
