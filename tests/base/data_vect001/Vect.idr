import Data.Vect

takeFromStream : List (n ** Vect n Int)
takeFromStream = [(n ** take n [3..]) | n <- [0, 1, 5]]

unsnocCases : List (n ** (Vect n Nat, Nat))
unsnocCases = [
      (_ ** unsnoc [3])
    , (_ ** unsnoc [3, 4])
    , (_ ** unsnoc [3, 4, 5])
  ]

scanrMul : List (n ** Vect n Nat)
scanrMul = [
      (_ ** scanr (*) 2 [])
    , (_ ** scanr (*) 2 [3])
    , (_ ** scanr (*) 2 [5, 4, 3])
  ]

scanrCons : Vect 4 (List Nat)
scanrCons = scanr (::) Nil [2, 3, 4]

scanr1Mul : List (n ** Vect n Nat)
scanr1Mul = [
      (_ ** scanr1 (*) [3])
    , (_ ** scanr1 (*) [5, 4, 3])
  ]

main : IO ()
main = do
  printLn takeFromStream
  printLn unsnocCases
  printLn scanrMul
  printLn scanrCons
  printLn scanr1Mul
