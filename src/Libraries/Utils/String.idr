module Libraries.Utils.String

%default total

export
dotSep : List String -> String
dotSep [] = ""
dotSep [x] = x
dotSep (x :: xs) = x ++ concat ["." ++ y | y <- xs]

export
stripQuotes : (count : Nat) -> (str : String) -> String
stripQuotes count str = substr count (length str `minus` (2 * count)) str

export
lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = assert_total (isLower (prim__strHead str))
