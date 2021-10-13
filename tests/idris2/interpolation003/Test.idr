import Data.String

Interpolation Bool where
  interpolate True = "TT"
  interpolate False = "FF"

Interpolation Nat where
  interpolate Z = "0"
  interpolate (S n) = "S \{n}"

Interpolation Integer where
  interpolate = show

test : String
test = "\{2}\{True}: \{True}\{True}"
