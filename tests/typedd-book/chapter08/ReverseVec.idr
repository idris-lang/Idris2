import Data.Nat
import Data.Vect

myReverse1 : Vect n a -> Vect n a
myReverse1 [] = []
myReverse1 {n = S k} (x :: xs)
        = let result = myReverse1 xs ++ [x] in
              rewrite plusCommutative 1 k in result

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
  where
    reverseProof : Vect (k + 1) a -> Vect (S k) a
    reverseProof {k} result = rewrite plusCommutative 1 k in result
