module Data.String.Extra

import Data.Nat
import Data.String

%default total

infixl 5 +>
infixr 5 <+

||| Adds a character to the end of the specified string.
|||
||| ```idris example
||| strSnoc "AB" 'C'
||| ```
||| ```idris example
||| strSnoc "" 'A'
||| ```
public export
strSnoc : String -> Char -> String
strSnoc s c = s ++ (singleton c)

||| Alias of `strSnoc`
|||
||| ```idris example
||| "AB" +> 'C'
||| ```
public export
(+>) : String -> Char -> String
(+>) = strSnoc

||| Alias of `strCons`
|||
||| ```idris example
||| 'A' <+ "AB"
||| ```
public export
(<+) : Char -> String -> String
(<+) = strCons

||| Take the first `n` characters from a string. Returns the whole string
||| if it's too short.
public export
take : (n : Nat) -> (input : String) -> String
take n str = substr Z n str

||| Take the last `n` characters from a string. Returns the whole string
||| if it's too short.
public export
takeLast : (n : Nat) -> (input : String) -> String
takeLast n str with (length str)
  takeLast n str | len with (isLTE n len)
    takeLast n str | len | Yes prf = substr (len `minus` n) len str
    takeLast n str | len | No contra = str

||| Remove the first `n` characters from a string. Returns the empty string if
||| the input string is too short.
public export
drop : (n : Nat) -> (input : String) -> String
drop n str = substr n (length str) str

||| Remove the last `n` characters from a string. Returns the empty string if
||| the input string is too short.
public export
dropLast : (n : Nat) -> (input : String) -> String
dropLast n str = reverse (drop n (reverse str))

||| Remove the first and last `n` characters from a string. Returns the empty
||| string if the input string is too short.
public export
shrink : (n : Nat) -> (input : String) -> String
shrink n str = dropLast n (drop n str)

||| Concatenate the strings from a `Foldable` containing strings, separated by
||| the given string.
public export
join : (sep : String) -> Foldable t => (xs : t String) -> String
join sep xs = drop (length sep)
                   (foldl (\acc, x => acc ++ sep ++ x) "" xs)

||| Get a character from a string if the string is long enough.
public export
index : (n : Nat) -> (input : String) -> Maybe Char
index n str with (unpack str)
  index n str | [] = Nothing
  index Z str | (x :: xs) = Just x
  index (S n) str | (x :: xs) = index n str | xs

||| Indent each line of a given string by `n` spaces.
public export
indentLines : (n : Nat) -> String -> String
indentLines n str = unlines $ map (indent n) $ lines str

||| Left-justify a string to the given length, using the
||| specified fill character on the right.
export
justifyLeft : Nat -> Char -> String -> String
justifyLeft n c s = s ++ replicate (n `minus` length s) c

||| Right-justify a string to the given length, using the
||| specified fill character on the left.
export
justifyRight : Nat -> Char -> String -> String
justifyRight n c s = replicate (n `minus` length s) c ++ s

||| Truncates a string to the given length.
||| If the given string is longer, replace first characters with given prefix.
|||
||| Say, `leftEllipsis 5 ".." "abcdefgh"` should give `"..fgh"` and
||| `leftEllipsis 5 "" "abcdefgh"` should give `"defgh"`.
|||
||| Notice, that the resulting string can be longer than max length if the prefix is longer.
export
leftEllipsis : (maxLen : Nat) -> (pref : String) -> String -> String
leftEllipsis maxLen pref str = do
 let len = length str
 case len `isLTE` maxLen of
   Yes _ => str
   No _  => pref ++ substr ((len + length pref) `minus` maxLen) len str

||| Truncates a string to the given length.
||| If the given string is longer, replace last characters with given suffix.
|||
||| Say, `rightEllipsis 5 ".." "abcdefgh"` should give `"abc.."` and
||| `rightEllipsis 5 "" "abcdefgh"` should give `"abcde"`.
|||
||| Notice, that the resulting string can be longer than max length if the suffix is longer.
export
rightEllipsis : (maxLen : Nat) -> (suff : String) -> String -> String
rightEllipsis maxLen suff str = do
  let len = length str
  case len `isLTE` maxLen of
    Yes _ => str
    No _  => take (maxLen `minus` length suff) str ++ suff
