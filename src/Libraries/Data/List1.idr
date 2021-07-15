module Libraries.Data.List1

import Data.List1

%default total

-- TODO: Remove this, once Data.List1.unsnoc from base is available
--       to the compiler
export
unsnoc : (xs : List1 a) -> (List a, a)
unsnoc (h ::: Nil)       = (Nil, h)
unsnoc (h ::: (x :: xs)) =
  let (ini,lst) = Libraries.Data.List1.unsnoc (x ::: xs)
   in (h :: ini, lst)
