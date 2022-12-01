import Data.Vect

myReverse : Vect n el -> Vect n el
myReverse [] = []
myReverse {n = S k} (x :: xs) =
    replace {p=\n => Vect n el} (plusCommutative k 1) (myReverse xs ++ [x])
