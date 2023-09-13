module Temp

import Data.List

foo : (l : List Int) -> String -> String
foo l "length" with (length l)
  foo l "length" | 0 = "Zero"
  foo l "length" | n = "Not Zero"
foo l s = "Other"
