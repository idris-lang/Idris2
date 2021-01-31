module RawString

withWrap : String
withWrap = "foo
bar"

withIndent : String
withIndent = "foo
  bar"

withEscape : String
withEscape = #""foo"\#n
  \bar"#

test : IO ()
test =
  do
    putStrLn withWrap
    putStrLn withIndent
    putStrLn withEscape
    putStrLn ##"
name: #"foo"
version: "bar"
bzs: \#\'a\n\t\\'"##
