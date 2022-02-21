import Data.String

%hide interpDefault

Interpolation String where
  interpolate x = x

Interpolation Bool where
  interpolate True = "TT"
  interpolate False = "FF"

Interpolation Nat where
  interpolate Z = "0"
  interpolate (S n) = "S \{n}"

Interpolation Integer where
  interpolate = show

test : List String
test = [
    "This is \{True}",
    "This is \{False}",
    "This is a number : \{S (S (S Z))}",
    "\{2}\{True}: \{True}\{True}"
  ]
