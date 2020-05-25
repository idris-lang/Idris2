module Utils.String

%default total

export
dotSep : List String -> String
dotSep [] = ""
dotSep [x] = x
dotSep (x :: xs) = x ++ concat ["." ++ y | y <- xs]

export
stripQuotes : (str : String) -> String
stripQuotes str = substr 1 (length str `minus` 2) str
