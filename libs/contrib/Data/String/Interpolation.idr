||| A DYI version of 'string interpolation', mimicking Python 3's 'f-string' syntax
||| Not as fancy
module Data.String.Interpolation

namespace Data.String.Interpolation.Basic
  %inline
  public export
  F : List String -> String
  F strs = concat (strs)

namespace Data.String.Interpolation.Nested
  %inline
  public export
  F : List (List String) -> String
  F strss = F (concat strss)

{- Examples:
fstring : String
fstring = let apples = "apples" in
          F["I have some ", apples," here."]                     --- cf. f"I have some {apples} here."

multiline : String
multiline = let name = "Edwin"
                profession = "Hacker"
                affiliation = "the University of St. Andrews" in --- cf.
                F [["Hi ",name,". "             ]                --- f"Hi {name}. "              \
                  ,["You are a ",profession,". "]                --- f"You are a {profession}. " \
                  ,["You were in ",affiliation,"."]              --- f"You were in {affiliation}."
                  ]

-}
