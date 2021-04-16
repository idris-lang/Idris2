module Libraries.Text.PrettyPrint.Prettyprinter.Render.HTML

import Data.List
import Data.String

import Idris.Version

export
htmlEscape : String -> String
htmlEscape s = fastAppend $ reverse $ go [] s
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

export
htmlPreamble : String -> String -> String -> String
htmlPreamble title root class = """
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <title>
""" ++ htmlEscape title ++ """
    </title>
    <link rel="stylesheet" href="
""" ++ root ++ """
styles.css">
  </head>
  <body class="
""" ++ class ++ """
">
    <header>
      <strong>Idris2Doc</strong> :
""" ++ " " ++ htmlEscape title ++ """
      <nav>
        <a href="
""" ++ root ++ """
index.html">Index</a>
      </nav>
    </header>
    <div class="container">
"""

export
htmlFooter : String
htmlFooter = "</div><footer>Produced by Idris 2 version " ++ (showVersion True version) ++ "</footer></body></html>"
