import Data.Vect

oneInVector : Elem 1 [1,2,3]
oneInVector = Here

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

fourNotInVector : Elem 4 [1,2,3] -> Void
fourNotInVector (There (There (There Here))) impossible
fourNotInVector (There (There (There (There _)))) impossible

peteNotInVector : Elem "Pete" ["John", "Paul", "George", "Ringo"] -> Void
peteNotInVector (There (There (There (There Here)))) impossible
peteNotInVector (There (There (There (There (There _))))) impossible
