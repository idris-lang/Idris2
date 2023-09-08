import Data.Vect

nums : List (Int, Int)
nums = [(1, 2), (3, 4), (5, 6)]

addToNums : List (Int, Int) -> List (Int, Int)
addToNums = map (\ (x, y) => (x + 1, y + 1))

vects : List (n ** Vect n Int)
vects = [(_ ** [1,2,3]),
         (_ ** [1,2,3,4]),
         (_ ** [1,2,3,4,5])]

lengths : List (n ** Vect n a) -> List Nat
lengths = map (\ (len ** xs) => length xs)
