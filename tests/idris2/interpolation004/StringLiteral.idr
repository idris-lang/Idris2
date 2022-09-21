module StringLiteral

Str : String
Str = """
  First line

  Third line
  """

Str2NL : String
Str2NL = "First line\n\nThird line"

sss : Str === Str2NL
sss = Refl

Str1NL : String
Str1NL = "First line\nThird line"

sss' : (Str == Str1NL) === False
sss' = Refl
