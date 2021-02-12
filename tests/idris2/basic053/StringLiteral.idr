module StringLiteral

withWrap : String
withWrap = "foo
bar"

withNoWrap : String
withNoWrap = "foo \
bar"

withIndent : String
withIndent = "foo
  bar"

withEscape : String
withEscape = #""foo"\#n
  \bar"#

withEscapeNoWrap : String
withEscapeNoWrap = #""foo" \#
  \bar"#

interp : String
interp = "\{withNoWrap}"

interp2 : String
interp2 = "hello\{ " " ++ ##"world\##{#"."#}"## }"

test : IO ()
test =
  do
    putStrLn withWrap
    putStrLn withNoWrap
    putStrLn withIndent
    putStrLn withEscape
    putStrLn withEscapeNoWrap
    putStrLn interp
    putStrLn interp2
    let idris = "Idris"
    putStrLn "Hello \{idris ++ show 2}!"
    putStrLn ##"
name: #"foo"
version: "bar"
bzs: \#\'a\n\t\\'"##
