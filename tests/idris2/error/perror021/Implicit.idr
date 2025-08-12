import Data.Vect

myReplace : x === y -> p x -> p y
myReplace Refl px = px

myReverse : Vect n el -> Vect n el
myReverse [] = []
myReverse {n = S k} (x :: xs) =
    myReplace {p=\n => Vect n el} (plusCommutative k 1) (myReverse xs ++ [x])
