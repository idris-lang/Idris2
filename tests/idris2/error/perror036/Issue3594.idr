module BracketFailure

data Color : Type where
  Red : Color
  Blue : Color

implementation Show Color where
  show Red = "red
  show Blue = "blue"

