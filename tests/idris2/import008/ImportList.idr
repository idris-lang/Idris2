import Data.List using (take, find, lenght)
import Data.Vect hiding (find)

f : List a -> List a
f = take 1

g : Ord a => List a -> List a
g = sort
