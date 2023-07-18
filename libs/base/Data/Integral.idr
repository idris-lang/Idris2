module Data.Integral

export
even : Integral n => Eq n => n -> Bool
even n = n `mod` 2 == 0

export
odd : Integral n => Eq n => n -> Bool
odd = not . even
