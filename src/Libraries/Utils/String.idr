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
lowerFirst str = isLower $ assert_total $ prim__strHead str

escapeGeneric : Char -> List Char -> String -> String
escapeGeneric esc toEscape = pack . foldr escape [] . unpack
  where
    escape : Char -> List Char -> List Char
    escape c cs =
      if elem c toEscape
        then (esc :: c :: cs)
        else (c :: cs)

export
escapeStringUnix : String -> String
escapeStringUnix = escapeGeneric '\\' ['"', '\\']

export
escapeStringChez : String -> String
escapeStringChez = escapeGeneric '\\' ['\'', '\\']
