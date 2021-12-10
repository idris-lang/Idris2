import Data.List using  (take, find, lentgh) renaming (snoc to listSnoc)
import Data.Vect hiding (find)               renaming (snoc to vectSnoc)

import Data.These renaming (these to e)

f : List a -> List a
f = take 1

g : Ord a => List a -> List a
g = sort

h : (a -> Bool) -> Vect n a -> Maybe a
h = find
