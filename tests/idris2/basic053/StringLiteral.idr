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

interp3 : String
interp3 = "Just 1 + Just 2 = \{
  show $ do a <- Just 1
            b <- Just 2
            Just (a + b)
}"

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
    putStrLn interp3
    let idris = "Idris"
    putStrLn "Hello \{idris ++ show 2}!"
    putStrLn ##"
name: #"foo"
version: "bar"
bzs: \#\'a\n\t\\'"##
