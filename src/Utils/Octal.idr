module Utils.Octal

import Data.Primitives.Views

%default total

octDigit : Int -> Char
octDigit 0 = '0'
octDigit 1 = '1'
octDigit 2 = '2'
octDigit 3 = '3'
octDigit 4 = '4'
octDigit 5 = '5'
octDigit 6 = '6'
octDigit 7 = '7'
octDigit _ = 'X' -- TMP HACK: Ideally we'd have a bounds proof, generated below

||| Convert a positive integer into a list of octal characters
export
asOct : Int -> String
asOct n = pack $ asOct' n []
  where
    asOct' : Int -> List Char -> List Char
    asOct' 0 oct = oct
    asOct' n oct with (n `divides` 8)
      asOct' (8 * div + rem) oct | DivBy div rem _ =
        assert_total $ asOct' div (octDigit rem :: oct)

export
fromOctDigit : Char -> Maybe Int
fromOctDigit '0' = Just 0
fromOctDigit '1' = Just 1
fromOctDigit '2' = Just 2
fromOctDigit '3' = Just 3
fromOctDigit '4' = Just 4
fromOctDigit '5' = Just 5
fromOctDigit '6' = Just 6
fromOctDigit '7' = Just 7
fromOctDigit _ = Nothing

export
fromOctChars : List Char -> Maybe Int
fromOctChars = fromOctChars' 1
  where
    fromOctChars' : Int -> List Char -> Maybe Int
    fromOctChars' _ [] = Just 0
    fromOctChars' m (d :: ds) = pure $ !(fromOctDigit (toLower d)) * m + !(fromOctChars' (m*8) ds)

export
fromOct : String -> Maybe Int
fromOct = fromOctChars . unpack

