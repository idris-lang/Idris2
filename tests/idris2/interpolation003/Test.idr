
Interpolation Bool where
  interpolate True = "TT"
  interpolate False = "FF"

Interpolation Nat where
  interpolate Z = "0"
  interpolate (S n) = "S \{n}"
