module Text.PrettyPrint.Prettyprinter.Render.HTML

import Data.String

%default covering

export
htmlEscape : String -> String
htmlEscape s = fastConcat $ reverse $ go [] s
  where
    isSafe : Char -> Bool
    isSafe '"' = False
    isSafe '<' = False
    isSafe '>' = False
    isSafe '&' = False
    isSafe '\'' = False
    isSafe '\t' = True
    isSafe '\n' = True
    isSafe '\r' = True
    isSafe c = (c >= ' ' && c <= '~')

    htmlQuote : Char -> String
    htmlQuote '"' = "&quot;"
    htmlQuote '<' = "&lt;"
    htmlQuote '>' = "&gt;"
    htmlQuote '&' = "&amp;"
    htmlQuote '\'' = "&apos;"
    htmlQuote c = "&#" ++ (show $ ord c) ++ ";"

    go : List String -> String -> List String
    go acc "" = acc
    go acc s =
      case span isSafe s of
           (safe, "") => safe::acc
           (safe, rest) => let c = assert_total (strIndex rest 0)
                               escaped = htmlQuote c in
                               go (escaped::safe::acc) (assert_total $ strTail rest)
