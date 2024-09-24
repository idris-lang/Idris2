module Language.JSON.Data

import Data.Bits
import Data.List
import Data.String.Extra
import Data.String

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

public export
Eq JSON where
    JNull == JNull = True
    JBoolean x == JBoolean y = x == y
    JNumber x == JNumber y = x == y
    JString x == JString y = x == y
    JArray xs == JArray ys = assert_total $ xs == ys
    JObject xs == JObject ys = assert_total $ on (==) (sortBy $ compare `on` fst) xs ys
    _ == _ = False

private
b16ToHexString : Bits16 -> String
b16ToHexString n =
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
    other => assert_total $
               b16ToHexString (n `shiftR` 4) ++
               b16ToHexString (n .&. 15)

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
                 then let hex = b16ToHexString (cast $ ord c)
                       in "\\u" ++ justifyRight 4 '0' hex
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

export
[Idris] Show JSON where
  showPrec d JNull = "JNull"
  showPrec d (JBoolean x) = showCon d "JBoolean" $ showArg x
  showPrec d (JNumber x) = showCon d "JNumber" $ showArg x
  showPrec d (JString x) = showCon d "JString" $ showArg x
  showPrec d (JArray xs) = assert_total $ showCon d "JArray" $ showArg xs
  showPrec d (JObject xs) = assert_total $ showCon d "JObject" $ showArg xs

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

public export
Cast () JSON where
  cast () = JNull

public export
Cast Bool JSON where
  cast = JBoolean

public export
Cast Double JSON where
  cast = JNumber

public export
Cast String JSON where
  cast = JString

public export
Cast a JSON => Cast (List a) JSON where
  cast xs = JArray $ map cast xs

public export
lookup : String -> JSON -> Maybe JSON
lookup key (JObject xs) = lookup key xs
lookup key json = Nothing

public export
update : (Maybe JSON -> Maybe JSON) -> String -> JSON -> JSON
update f key (JObject xs) = JObject $ updateAttr f key xs
  where
    updateAttr : (Maybe JSON -> Maybe JSON) -> String -> List (String, JSON) -> List (String, JSON)
    updateAttr f key [] = do
        let Just y = f Nothing
            | Nothing => []
        [(key, y)]
    updateAttr f key ((nm, x) :: xs) = if key == nm
        then do
            let Just y = f (Just x)
                | Nothing => xs
            (nm, y) :: xs
        else (nm, x) :: updateAttr f key xs
update f key json = json

public export
traverseJSON : Monad m => (JSON -> m JSON) -> JSON -> m JSON
traverseJSON f (JArray xs) = do
    xs <- assert_total $ traverse (traverseJSON f) xs
    f $ JArray xs
traverseJSON f (JObject xs) = do
    xs <- traverse (assert_total $ bitraverse pure $ traverseJSON f) xs
    f $ JObject xs
traverseJSON f json = f json

public export
traverseJSON_ : Monad m => (JSON -> m ()) -> JSON -> m ()
traverseJSON_ f json = ignore $ traverseJSON (\x => f x *> pure x) json
