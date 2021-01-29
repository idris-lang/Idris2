module RawString

configTemplate : String
configTemplate =
"""name: "foo"
version: "bar"
bzs: \'a\n\t\\'
"""

test : IO ()
test =
  do
    putStr configTemplate
    putStr """foo
bar
baz
"""
