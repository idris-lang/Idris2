module Libraries.Data.String

import Data.String

%default total

-- Remove as soon as 0.9.0 is released,
-- (together with its imports in Idris.IDEMode.CaseSplit and Idris.REPL)
-- as rtrim is being moved to Data.String in base

||| Trim whitespace on the right of the string
public export
rtrim : String -> String
rtrim = reverse . ltrim . reverse
