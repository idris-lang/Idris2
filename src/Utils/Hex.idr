module Utils.Hex

import Data.List
import Data.Primitives.Views

%default total

hexDigit : Int -> Char
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

||| Convert a positive integer into a list of (lower case) hexadecimal characters
export
asHex : Int -> String
asHex n =
  if n > 0
    then pack $ asHex' n []
    else "0"
  where
    asHex' : Int -> List Char -> List Char
    asHex' 0 hex = hex
    asHex' n hex with (n `divides` 16)
      asHex' (16 * div + rem) hex | DivBy div rem _ =
        asHex' (assert_smaller n div) (hexDigit rem :: hex)

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
fromHexChars : List Char -> Maybe Int
fromHexChars = fromHexChars' 1
  where
    fromHexChars' : Int -> List Char -> Maybe Int
    fromHexChars' _ [] = Just 0
    fromHexChars' m (d :: ds) = pure $ !(fromHexDigit (toLower d)) * m + !(fromHexChars' (m*16) ds)

export
fromHex : String -> Maybe Int
fromHex = fromHexChars . unpack
