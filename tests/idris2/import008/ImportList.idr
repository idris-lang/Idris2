import Data.List using (take, lenght)

f : Ord a => List a -> List a
f = take 1

g : Ord a => List a -> List a
g = sort
