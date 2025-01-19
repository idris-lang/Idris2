module StringLiterals

hello : FromString a => a
hello = "Hello"

helloName : String -> String
helloName name = "\{hello {a = String}} \{name}"

welcomeName : String -> String
welcomeName name = """
  \{helloName name}
  and welcome!
  """

scareQuotes : String
scareQuotes = #""hello""#

test : StringLiterals.scareQuotes = "\"hello\""
test = Refl
