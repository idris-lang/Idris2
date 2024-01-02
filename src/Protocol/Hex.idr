module Protocol.Hex

import Data.Bits
import Data.List

%default total

hexDigit : Bits64 -> Char
hexDigit 0 = '0'
hexDigit 1 = '1'
hexDigit 2 = '2'
hexDigit 3 = '3'
hexDigit 4 = '4'
hexDigit 5 = '5'
hexDigit 6 = '6'
hexDigit 7 = '7'
hexDigit 8 = '8'
hexDigit 9 = '9'
hexDigit 10 = 'a'
hexDigit 11 = 'b'
hexDigit 12 = 'c'
hexDigit 13 = 'd'
hexDigit 14 = 'e'
hexDigit 15 = 'f'
hexDigit _ = 'X' -- TMP HACK: Ideally we'd have a bounds proof, generated below

||| Convert a Bits64 value into a list of (lower case) hexadecimal characters
export
asHex : Bits64 -> String
asHex 0 = "0"
asHex n = pack $ asHex' n []
  where
    asHex' : Bits64 -> List Char -> List Char
    asHex' 0 hex = hex
    asHex' n hex = asHex' (assert_smaller n (n `shiftR` 4)) (hexDigit (n .&. 0xf) :: hex)

export
leftPad : Char -> Nat -> String -> String
leftPad paddingChar padToLength str =
  if length str < padToLength
    then pack (List.replicate (minus padToLength (length str)) paddingChar) ++ str
    else str

export
fromHexDigit : Char -> Maybe Int
fromHexDigit '0' = Just 0
fromHexDigit '1' = Just 1
fromHexDigit '2' = Just 2
fromHexDigit '3' = Just 3
fromHexDigit '4' = Just 4
fromHexDigit '5' = Just 5
fromHexDigit '6' = Just 6
fromHexDigit '7' = Just 7
fromHexDigit '8' = Just 8
fromHexDigit '9' = Just 9
fromHexDigit 'a' = Just 10
fromHexDigit 'b' = Just 11
fromHexDigit 'c' = Just 12
fromHexDigit 'd' = Just 13
fromHexDigit 'e' = Just 14
fromHexDigit 'f' = Just 15
fromHexDigit _ = Nothing

export
fromHexChars : List Char -> Maybe Integer
fromHexChars = fromHexChars' 1
  where
    fromHexChars' : Integer -> List Char -> Maybe Integer
    fromHexChars' _ [] = Just 0
    fromHexChars' m (d :: ds)
      = do digit <- fromHexDigit (toLower d)
           digits <- fromHexChars' (m*16) ds
           pure $ cast digit * m + digits

export
fromHex : String -> Maybe Integer
fromHex = fromHexChars . unpack
