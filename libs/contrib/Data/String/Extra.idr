module Data.String.Extra

import Data.List
import Data.List1
import Data.Nat
import Data.Strings

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

||| Produce a string by repeating the character `c` `n` times.
public export
replicate : (n : Nat) -> (c : Char) -> String
replicate n c = pack $ replicate n c

||| Indent a given string by `n` spaces.
public export
indent : (n : Nat) -> String -> String
indent n x = replicate n ' ' ++ x

||| Indent each line of a given string by `n` spaces.
public export
indentLines : (n : Nat) -> String -> String
indentLines n str = unlines $ map (indent n) $ forget $ lines str

||| Return a string of the given character repeated
||| `n` times.
export
fastReplicate : (n : Nat) -> Char -> String
fastReplicate n c = fastPack $ replicate n c

||| Left-justify a string to the given length, using the
||| specified fill character on the right.
export
justifyLeft : Nat -> Char -> String -> String
justifyLeft n c s = s ++ fastReplicate (n `minus` length s) c

||| Right-justify a string to the given length, using the
||| specified fill character on the left.
export
justifyRight : Nat -> Char -> String -> String
justifyRight n c s = fastReplicate (n `minus` length s) c ++ s
