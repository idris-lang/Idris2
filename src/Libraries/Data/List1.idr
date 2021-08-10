module Libraries.Data.List1

import Data.List1

%default total

-- TODO: Remove this, once Data.List1.unsnoc from base is available
--       to the compiler

export
unsnoc : (xs : List1 a) -> (List a, a)
unsnoc (x ::: xs) = go x xs where

  go : (x : a) -> (xs : List a) -> (List a, a)
  go x [] = ([], x)
  go x (y :: ys) = let (ini,lst) = go y ys
                   in (x :: ini, lst)
