module StringLiteral

rawStr : String
rawStr = #""""""#

interp1 : String
interp1 = "Just 1 + Just 2 = \{
  show $ do a <- Just 1
            b <- Just 2
            Just (a + b)
}"

interp2 : String
interp2 = "hello\{ " " ++ ##"world\##{#"."#}"## }"

multi1 : String
multi1 = """
  [project]
  name: "project"
  version: "0.1.0"
  [deps]
  "semver" = 0.2
  """

multi2 : String
multi2 = #"""
            a\#
             b\n
              \#{"c"}
            """#

multi3 : String
multi3 = """
  \{"sticking"} \{"together"}\{
 ""}\{#"""
!

"""#}
  """

multi4 : String
multi4 = """
  A very very \n\nvery very very \n
  very long string. \
  """

test : IO ()
test = do
    putStrLn rawStr
    putStrLn interp1
    putStrLn interp2
    let idris = "Idris"
    putStrLn "Hello \{idris ++ show 2}!"
    putStrLn multi1
    putStrLn multi2
    putStrLn multi3
    putStrLn multi4
    putStrLn """
    """
    putStrLn ##"""
a
"""##
    putStrLn ##"""
name: #"foo"
version: "bar"
bzs: \#\'a\n\t\\'
"""
"""##
    printLn "contains\NULcharacter"
