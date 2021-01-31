module RawString

test1 : String
test1 = r"foo
 bar
#baz
###blabla
 "

test2 : String
test2 = r#"
name: "foo"
version: "bar"
bzs: \'a\n\t\\'"#

test : IO ()
test =
  do
    putStrLn test1
    putStrLn test2
    putStrLn r##""#bar
"##
