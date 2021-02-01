module RawString

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

test : IO ()
test =
  do
    putStrLn withWrap
    putStrLn withNoWrap
    putStrLn withIndent
    putStrLn withEscape
    putStrLn withEscapeNoWrap
    putStrLn ##"
name: #"foo"
version: "bar"
bzs: \#\'a\n\t\\'"##
