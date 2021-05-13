module Libraries.Data.List1

import public Data.List1

%default total

-- TODO: Remove this, once Data.List1.fromList from base is available
--       to the compiler

public export
fromList : List a -> Maybe (List1 a)
fromList [] = Nothing
fromList (x :: xs) = Just (x ::: xs)

-- TODO: Remove this, once Data.List1.unsnoc from base is available
--       to the compiler
export
unsnoc : (xs : List1 a) -> (List a, a)
unsnoc (h ::: Nil)       = (Nil, h)
unsnoc (h ::: (x :: xs)) =
  let (ini,lst) = Libraries.Data.List1.unsnoc (x ::: xs)
   in (h :: ini, lst)
