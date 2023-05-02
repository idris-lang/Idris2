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

permutation : Vect 4 Char
permutation = permute ['a', 'b', 'c', 'd'] [0, 3, 2, 1]

split2by4 : Vect 2 (Vect 4 Nat)
split2by4 = kSplits 2 4 [1, 2, 3, 4, 5, 6, 7, 8]

split4by2 : Vect 4 (Vect 2 Nat)
split4by2 = nSplits 2 4 [1, 2, 3, 4, 5, 6, 7, 8]

genNoFins : Vect 0 (Fin 0)
genNoFins = allFins 0

gen3Fins : Vect 3 (Fin 3)
gen3Fins = allFins 3

main : IO ()
main = do
  printLn takeFromStream
  printLn unsnocCases
  printLn scanrMul
  printLn scanrCons
  printLn scanr1Mul
  printLn permutation
  printLn split2by4
  printLn split4by2
  printLn genNoFins
  printLn gen3Fins
