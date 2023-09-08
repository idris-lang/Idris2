
toBit : Num i => Char -> Maybe i
toBit '0' = Just 0
toBit '1' = Just 1
toBit _ = Nothing

-- Return the number represented in binary as an initial segment of
-- the string (remembering that if a number begins 0, it's zero).
eatBinary : (Eq i, Num i) => String -> i
eatBinary = firstDigit . unpack where

  laterDigit : i -> List Char -> i
  laterDigit n [] = n
  laterDigit n (d :: ds) = let
    f : Maybe i -> i
    f Nothing = n
    f (Just a) = laterDigit (2*n + a) ds
    in f $ toBit d

  firstDigit : List Char -> i
  firstDigit [] = 0
  firstDigit (d :: ds) = let
    f : Maybe i -> i
    f Nothing = 0
    f (Just 0) = 0
    f (Just a) = laterDigit a ds
    in f $ toBit d
