module Parser.Support

import public Text.Lexer
import public Text.Parser

import Core.TT
import Data.List
import Data.List.Views
import Parser.Unlit
import System.File

%default total

public export
data ParseError tok
  = ParseFail String (Maybe (Int, Int)) (List tok)
  | LexFail   (Int, Int, String)
  | FileFail  FileError
  | LitFail   LiterateError

export
Show tok => Show (ParseError tok) where
  show (ParseFail err loc toks)
      = "Parse error: " ++ err ++ " (next tokens: "
            ++ show (take 10 toks) ++ ")"
  show (LexFail (c, l, str))
      = "Lex error at " ++ show (c, l) ++ " input: " ++ str
  show (FileFail err)
      = "File error: " ++ show err
  show (LitFail (MkLitErr l c str))
      = "Lit error(s) at " ++ show (c, l) ++ " input: " ++ str

export
toGenericParsingError : ParsingError (TokenData token) -> ParseError token
toGenericParsingError (Error err [])      = ParseFail err Nothing []
toGenericParsingError (Error err (t::ts)) = ParseFail err (Just (line t, col t)) (map tok (t::ts))

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

escape' : List Char -> Maybe (List Char)
escape' [] = pure []
escape' ('\\' :: '\\' :: xs) = pure $ '\\' :: !(escape' xs)
escape' ('\\' :: '&' :: xs) = pure !(escape' xs)
escape' ('\\' :: 'a' :: xs) = pure $ '\a' :: !(escape' xs)
escape' ('\\' :: 'b' :: xs) = pure $ '\b' :: !(escape' xs)
escape' ('\\' :: 'f' :: xs) = pure $ '\f' :: !(escape' xs)
escape' ('\\' :: 'n' :: xs) = pure $ '\n' :: !(escape' xs)
escape' ('\\' :: 'r' :: xs) = pure $ '\r' :: !(escape' xs)
escape' ('\\' :: 't' :: xs) = pure $ '\t' :: !(escape' xs)
escape' ('\\' :: 'v' :: xs) = pure $ '\v' :: !(escape' xs)
escape' ('\\' :: '\'' :: xs) = pure $ '\'' :: !(escape' xs)
escape' ('\\' :: '\"' :: xs) = pure $ '\"' :: !(escape' xs)
escape' ('\\' :: 'x' :: xs)
    = case span isHexDigit xs of
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => pure $ cast !(toHex 1 (reverse ds)) ::
                                 !(assert_total (escape' rest))
  where
    toHex : Int -> List Char -> Maybe Int
    toHex _ [] = Just 0
    toHex m (d :: ds)
        = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)
escape' ('\\' :: 'o' :: xs)
    = case span isOctDigit xs of
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => pure $ cast !(toOct 1 (reverse ds)) ::
                                 !(assert_total (escape' rest))
  where
    toOct : Int -> List Char -> Maybe Int
    toOct _ [] = Just 0
    toOct m (d :: ds)
        = pure $ !(oct (toLower d)) * m + !(toOct (m*8) ds)
escape' ('\\' :: xs)
    = case span isDigit xs of
           ([], (a :: b :: c :: rest)) =>
               case getEsc (fastPack (the (List _) [a, b, c])) of
                   Just v => Just (v :: !(assert_total (escape' rest)))
                   Nothing => case getEsc (fastPack (the (List _) [a, b])) of
                                   Just v => Just (v :: !(assert_total (escape' (c :: rest))))
                                   Nothing => escape' xs
           ([], (a :: b :: [])) =>
               case getEsc (fastPack (the (List _) [a, b])) of
                   Just v => Just (v :: [])
                   Nothing => escape' xs
           ([], rest) => assert_total (escape' rest)
           (ds, rest) => Just $ cast (cast {to=Int} (fastPack ds)) ::
                                 !(assert_total (escape' rest))
escape' (x :: xs) = Just $ x :: !(escape' xs)

export
escape : String -> Maybe String
escape x = pure $ fastPack !(escape' (unpack x))

export
getCharLit : String -> Maybe Char
getCharLit str
   = do e <- escape str
        if length e == 1
           then Just (assert_total (prim__strHead e))
           else if length e == 0 -- parsed the NULL character that terminated the string!
                   then Just '\0000'
                   else Nothing
