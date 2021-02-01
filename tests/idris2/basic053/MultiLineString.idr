module MultiLineString

test1 : String
test1 = """
  [project]
  name: "project"
  version: "0.1.0"

  [deps]
  "semver" = 0.2
  """

test2 : String
test2 = """
            a
             b\n
              c
            """

test3 : String
test3 = """
  A very very very very very \
  very very very very very \
  very long string.\
  """

test4 : String
test4 = """
  A very very very very very \n
  very very very very very \n
  very long string.\n
  """

test5 : String
test5= #"""
  A very very very very very \n\#
  very very very very very \n
  very long string.\n
  """#

test : IO ()
test =
  do
    putStrLn test1
    putStrLn test2
    putStrLn test3
    putStrLn test4
    putStrLn test5
    putStrLn ###"""
        "a"
       b
      c\n
    """###
