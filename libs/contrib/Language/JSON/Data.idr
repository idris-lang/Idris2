module Language.JSON.Data

import Data.String.Extra
import Data.Strings
import Data.List

%default total

public export
data JSON
   = JNull
   | JBoolean Bool
   | JNumber Double
   | JString String
   | JArray (List JSON)
   | JObject (List (String, JSON))

%name JSON json


private
intToHexString : Int -> String
intToHexString n =
  case n of
    0 => "0"
    1 => "1"
    2 => "2"
    3 => "3"
    4 => "4"
    5 => "5"
    6 => "6"
    7 => "7"
    8 => "8"
    9 => "9"
    10 => "A"
    11 => "B"
    12 => "C"
    13 => "D"
    14 => "E"
    15 => "F"
    other => intToHexString (shiftR n 4) ++ intToHexString (mod n 16)

private
showChar : Char -> String
showChar c
  = case c of
         '\b' => "\\b"
         '\f' => "\\f"
         '\n' => "\\n"
         '\r' => "\\r"
         '\t' => "\\t"
         '\\' => "\\\\"
         '"'  => "\\\""
         c => if isControl c || c >= '\127'
--                 then "\\u" ++ b16ToHexString (fromInteger (cast (ord c)))
                 then "\\u" ++ intToHexString (ord c)-- quick hack until b16ToHexString is available in idris2
                 else singleton c

private
showString : String -> String
showString x = "\"" ++ concatMap showChar (unpack x) ++ "\""

||| Convert a JSON value into its string representation.
||| No whitespace is added.
private
stringify : JSON -> String
stringify JNull = "null"
stringify (JBoolean x) = if x then "true" else "false"
stringify (JNumber x) = show x
stringify (JString x) = showString x
stringify (JArray xs) = "[" ++ stringifyValues xs ++ "]"
  where
    stringifyValues : List JSON -> String
    stringifyValues [] = ""
    stringifyValues (x :: xs) = stringify x
                             ++ if isNil xs
                                   then ""
                                   else "," ++ stringifyValues xs
stringify (JObject xs) = "{" ++ stringifyProps xs ++ "}"
  where
    stringifyProp : (String, JSON) -> String
    stringifyProp (key, value) = showString key ++ ":" ++ stringify value

    stringifyProps : List (String, JSON) -> String
    stringifyProps [] = ""
    stringifyProps (x :: xs) = stringifyProp x
                            ++ if isNil xs
                                  then ""
                                  else "," ++ stringifyProps xs

export
Show JSON where
  show = stringify

||| Format a JSON value, indenting by `n` spaces per nesting level.
|||
||| @curr The current indentation amount, measured in spaces.
||| @n The amount of spaces to indent per nesting level.
export
format : {default 0 curr : Nat} -> (n : Nat) -> JSON -> String
format {curr} n json = indent curr $ formatValue curr n json
  where
    formatValue : (curr, n : Nat) -> JSON -> String
    formatValue _ _ (JArray []) = "[]"
    formatValue curr n (JArray xs@(_ :: _)) = "[\n" ++ formatValues xs
                                           ++ indent curr "]"
      where
        formatValues : (xs : List JSON) -> {auto ok : NonEmpty xs} -> String
        formatValues (x :: xs) = format {curr=(curr + n)} n x
                              ++ case xs of
                                      _ :: _ => ",\n" ++ formatValues xs
                                      [] => "\n"
    formatValue _ _ (JObject []) = "{}"
    formatValue curr n (JObject xs@(_ :: _)) = "{\n" ++ formatProps xs
                                            ++ indent curr "}"
      where
        formatProp : (String, JSON) -> String
        formatProp (key, value) = indent (curr + n) (showString key ++ ": ")
                               ++ formatValue (curr + n) n value

        formatProps : (xs : List (String, JSON)) -> {auto ok : NonEmpty xs} -> String
        formatProps (x :: xs) = formatProp x
                             ++ case xs of
                                     _ :: _ => ",\n" ++ formatProps xs
                                     [] => "\n"
    formatValue _ _ x = stringify x
