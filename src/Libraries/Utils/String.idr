module Libraries.Utils.String

%default total

export
dotSep : List String -> String
dotSep [] = ""
dotSep [x] = x
dotSep (x :: xs) = x ++ concat ["." ++ y | y <- xs]

export
stripSurrounds : (lead : Nat) -> (tail : Nat) -> String -> String
stripSurrounds lead tail str = substr lead (length str `minus` (lead + tail)) str

export
stripQuotes : String -> String
stripQuotes = stripSurrounds 1 1

export
lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = assert_total (isLower (prim__strHead str))
