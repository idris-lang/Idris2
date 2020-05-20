module Utils.String

%default total

export
stripQuotes : (str : String) -> String
stripQuotes str = prim__strSubstr 1 (lengthInt - 2) str
  where
    lengthInt : Int
    lengthInt = fromInteger. natToInteger . length $ str
