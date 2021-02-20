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

multi1 : String
multi1 = """
  [project]
  name: "project"
  version: "0.1.0"
  [deps]
  "semver" = 0.2
  """

multi2 : String
multi2 = """
            a
             b\n
              c
            """

multi3 : String
multi3 = """
  \{"sticking"} \{"together"}\{
 ""}\{"""
!

"""}
  """

multi4 : String
multi4 = """
  A very very very very very \n
  very very very\n\n very very \n
  very long string.
  """

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
    putStrLn interp
    putStrLn interp2
    putStrLn interp3
    let idris = "Idris"
    putStrLn "Hello \{idris ++ show 2}!"
    putStrLn multi1
    putStrLn multi2
    putStrLn multi3
    putStrLn multi4
    putStrLn """
  """
