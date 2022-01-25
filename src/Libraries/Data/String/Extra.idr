module Libraries.Data.String.Extra

import Data.List
import Data.List1
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

||| Indent a given string by `n` spaces.
public export
indent : (n : Nat) -> String -> String
indent n x = replicate n ' ' ++ x

||| Indent each line of a given string by `n` spaces.
public export
indentLines : (n : Nat) -> String -> String
indentLines n str = (join "\n") $ map (Extra.indent n) $ lines str
