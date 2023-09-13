module Parser.Support.Escaping

import Libraries.Data.String.Extra
import Data.List

export
hex : Char -> Maybe Int
hex '0' = Just 0
hex '1' = Just 1
hex '2' = Just 2
hex '3' = Just 3
hex '4' = Just 4
hex '5' = Just 5
hex '6' = Just 6
hex '7' = Just 7
hex '8' = Just 8
hex '9' = Just 9
hex 'a' = Just 10
hex 'b' = Just 11
hex 'c' = Just 12
hex 'd' = Just 13
hex 'e' = Just 14
hex 'f' = Just 15
hex _ = Nothing

export
dec : Char -> Maybe Int
dec '0' = Just 0
dec '1' = Just 1
dec '2' = Just 2
dec '3' = Just 3
dec '4' = Just 4
dec '5' = Just 5
dec '6' = Just 6
dec '7' = Just 7
dec '8' = Just 8
dec '9' = Just 9
dec _ = Nothing

export
oct : Char -> Maybe Int
oct '0' = Just 0
oct '1' = Just 1
oct '2' = Just 2
oct '3' = Just 3
oct '4' = Just 4
oct '5' = Just 5
oct '6' = Just 6
oct '7' = Just 7
oct _ = Nothing

export
getEsc : String -> Maybe Char
getEsc "NUL" = Just '\NUL'
getEsc "SOH" = Just '\SOH'
getEsc "STX" = Just '\STX'
getEsc "ETX" = Just '\ETX'
getEsc "EOT" = Just '\EOT'
getEsc "ENQ" = Just '\ENQ'
getEsc "ACK" = Just '\ACK'
getEsc "BEL" = Just '\BEL'
getEsc "BS" = Just '\BS'
getEsc "HT" = Just '\HT'
getEsc "LF" = Just '\LF'
getEsc "VT" = Just '\VT'
getEsc "FF" = Just '\FF'
getEsc "CR" = Just '\CR'
getEsc "SO" = Just '\SO'
getEsc "SI" = Just '\SI'
getEsc "DLE" = Just '\DLE'
getEsc "DC1" = Just '\DC1'
getEsc "DC2" = Just '\DC2'
getEsc "DC3" = Just '\DC3'
getEsc "DC4" = Just '\DC4'
getEsc "NAK" = Just '\NAK'
getEsc "SYN" = Just '\SYN'
getEsc "ETB" = Just '\ETB'
getEsc "CAN" = Just '\CAN'
getEsc "EM" = Just '\EM'
getEsc "SUB" = Just '\SUB'
getEsc "ESC" = Just '\ESC'
getEsc "FS" = Just '\FS'
getEsc "GS" = Just '\GS'
getEsc "RS" = Just '\RS'
getEsc "US" = Just '\US'
getEsc "SP" = Just '\SP'
getEsc "DEL" = Just '\DEL'
getEsc str = Nothing

unescape' : List Char -> List Char -> Maybe (List Char)
unescape' _ [] = pure []
unescape' escapeChars (x::xs)
    = assert_total $ if escapeChars `isPrefixOf` (x::xs)
         then case drop (length escapeChars) (x::xs) of
                   ('\\' :: xs) => pure $ '\\' :: !(unescape' escapeChars xs)
                   ('\n' :: xs) => pure !(unescape' escapeChars xs)
                   ('&' :: xs) => pure !(unescape' escapeChars xs)
                   ('a' :: xs) => pure $ '\a' :: !(unescape' escapeChars xs)
                   ('b' :: xs) => pure $ '\b' :: !(unescape' escapeChars xs)
                   ('f' :: xs) => pure $ '\f' :: !(unescape' escapeChars xs)
                   ('n' :: xs) => pure $ '\n' :: !(unescape' escapeChars xs)
                   ('r' :: xs) => pure $ '\r' :: !(unescape' escapeChars xs)
                   ('t' :: xs) => pure $ '\t' :: !(unescape' escapeChars xs)
                   ('v' :: xs) => pure $ '\v' :: !(unescape' escapeChars xs)
                   ('\'' :: xs) => pure $ '\'' :: !(unescape' escapeChars xs)
                   ('"' :: xs) => pure $ '"' :: !(unescape' escapeChars xs)
                   ('x' :: xs) => case span isHexDigit xs of
                                       ([], rest) => unescape' escapeChars rest
                                       (ds, rest) => pure $ cast !(toHex 1 (reverse ds)) ::
                                                             !(unescape' escapeChars rest)
                   ('o' :: xs) => case span isOctDigit xs of
                                       ([], rest) => unescape' escapeChars rest
                                       (ds, rest) => pure $ cast !(toOct 1 (reverse ds)) ::
                                                             !(unescape' escapeChars rest)
                   xs => case span isDigit xs of
                              ([], (a :: b :: c :: rest)) =>
                                case getEsc (fastPack [a, b, c]) of
                                     Just v => Just (v :: !(unescape' escapeChars rest))
                                     Nothing => case getEsc (fastPack [a, b]) of
                                                     Just v => Just (v :: !(unescape' escapeChars (c :: rest)))
                                                     Nothing => unescape' escapeChars xs
                              ([], (a :: b :: [])) =>
                                case getEsc (fastPack [a, b]) of
                                     Just v => Just (v :: [])
                                     Nothing => unescape' escapeChars xs
                              ([], rest) => unescape' escapeChars rest
                              (ds, rest) => Just $ cast (cast {to=Int} (fastPack ds)) ::
                                              !(unescape' escapeChars rest)
         else Just $ x :: !(unescape' escapeChars xs)
  where
    toHex : Int -> List Char -> Maybe Int
    toHex _ [] = Just 0
    toHex m (d :: ds)
        = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)

    toOct : Int -> List Char -> Maybe Int
    toOct _ [] = Just 0
    toOct m (d :: ds)
        = pure $ !(oct (toLower d)) * m + !(toOct (m*8) ds)

export
unescape : Nat -> String -> Maybe String
unescape hashtag x = let escapeChars = '\\' :: replicate hashtag '#' in
                       fastPack <$> (unescape' escapeChars (unpack x))
