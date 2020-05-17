module Utils.String

%default total

export
stripQuotes : String -> String
-- ASSUMPTION! Only total because we know we're getting quoted strings.
stripQuotes = assert_total (prim__strTail . reverse . prim__strTail . reverse)
