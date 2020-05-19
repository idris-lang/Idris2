longer : String -> String -> Nat
longer word1 word2
    = let len1 = length word1
          len2 = length word2 in
          if len1 > len2 then len1 else len2

pythagoras : Double -> Double -> Double
pythagoras x y = sqrt (square x + square y)
    where
      square : Double -> Double
      square x = x * x
