module Data.String

import Data.List
import Data.List1

%default total

export
singleton : Char -> String
singleton c = strCons c ""

||| Create a string by using n copies of a character
export
replicate : Nat -> Char -> String
replicate n c = pack (replicate n c)

||| Indent a given string by `n` spaces.
public export
indent : (n : Nat) -> String -> String
indent n x = replicate n ' ' ++ x

||| Pad a string on the left
export
padLeft : Nat -> Char -> String -> String
padLeft n c str = replicate (minus n (String.length str)) c ++ str

||| Pad a string on the right
export
padRight : Nat -> Char -> String -> String
padRight n c str = str ++ replicate (minus n (String.length str)) c

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 _ [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

partial
foldl1 : (a -> a -> a) -> List a -> a
foldl1 f (x::xs) = foldl f x xs

-- This uses fastConcat internally so it won't compute at compile time.
export
fastUnlines : List String -> String
fastUnlines = fastConcat . unlines'
  where unlines' : List String -> List String
        unlines' [] = []
        unlines' (x :: xs) = x :: "\n" :: unlines' xs

||| Splits a character list into a list of whitespace separated character lists.
|||
||| ```idris example
||| words' (unpack " A B C  D E   ")
||| ```
covering
words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' s''

||| Splits a string into a list of whitespace separated strings.
|||
||| ```idris example
||| words " A B C  D E   "
||| ```
export
covering
words : String -> List String
words s = map pack (words' (unpack s))

||| Joins the character lists by spaces into a single character list.
|||
||| ```idris example
||| unwords' [['A'], ['B', 'C'], ['D'], ['E']]
||| ```
unwords' : List (List Char) -> List Char
unwords' [] = []
unwords' ws = assert_total (foldr1 addSpace ws) where
  addSpace : List Char -> List Char -> List Char
  addSpace w s = w ++ (' ' :: s)

||| Joins the strings by spaces into a single string.
|||
||| ```idris example
||| unwords ["A", "BC", "D", "E"]
||| ```
export
unwords : List String -> String
unwords = pack . unwords' . map unpack

||| Splits a character list into a list of newline separated character lists.
|||
||| ```idris example
||| lines' (unpack "\rA BC\nD\r\nE\n")
||| ```
export
lines' : List Char -> List (List Char)
lines' s = linesHelp [] s
  where linesHelp : List Char -> List Char -> List (List Char)
        linesHelp [] [] = []
        linesHelp acc [] = [reverse acc]
        linesHelp acc ('\n' :: xs) = reverse acc :: linesHelp [] xs
        linesHelp acc ('\r' :: '\n' :: xs) = reverse acc :: linesHelp [] xs
        linesHelp acc ('\r' :: xs) = reverse acc :: linesHelp [] xs
        linesHelp acc (c :: xs) = linesHelp (c :: acc) xs


||| Splits a string into a list of newline separated strings.
|||
||| ```idris example
||| lines  "\rA BC\nD\r\nE\n"
||| ```
export
lines : String -> List String
lines s = map pack (lines' (unpack s))

||| Joins the character lists by a single character list by appending a newline
||| to each line.
|||
||| ```idris example
||| unlines' [['l','i','n','e'], ['l','i','n','e','2'], ['l','n','3'], ['D']]
||| ```
export
unlines' : List (List Char) -> List Char
unlines' [] = []
unlines' (l::ls) = l ++ '\n' :: unlines' ls

||| Joins the strings into a single string by appending a newline to each string.
|||
||| ```idris example
||| unlines ["line", "line2", "ln3", "D"]
||| ```
export
unlines : List String -> String
unlines = pack . unlines' . map unpack

%transform "fastUnlines" unlines = fastUnlines

||| A view checking whether a string is empty
||| and, if not, returning its head and tail
public export
data StrM : String -> Type where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

||| To each string we can associate its StrM view
public export
strM : (x : String) -> StrM x
strM "" = StrNil
strM x
  -- Using primitives, so `assert_total` and `believe_me` needed
    = assert_total $ believe_me $
        StrCons (prim__strHead x) (prim__strTail x)

||| A view of a string as a lazy linked list of characters
public export
data AsList : String -> Type where
  Nil  : AsList ""
  (::) : (c : Char) -> {str : String} -> Lazy (AsList str) -> AsList (strCons c str)

||| To each string we can associate the lazy linked list of characters
||| it corresponds to once unpacked.
public export
asList : (str : String) -> AsList str
asList str with (strM str)
  asList "" | StrNil = []
  asList str@(strCons x xs) | StrCons _ _ = x :: asList (assert_smaller str xs)

||| Trim whitespace on the left of the string
export
ltrim : String -> String
ltrim str with (asList str)
  ltrim ""  | [] = ""
  ltrim str@_ | x :: xs = if isSpace x then ltrim _ | xs else str

||| Trim whitespace on both sides of the string
export
trim : String -> String
trim = ltrim . reverse . ltrim . reverse

||| Splits the string into a part before the predicate
||| returns False and the rest of the string.
|||
||| ```idris example
||| span (/= 'C') "ABCD"
||| ```
||| ```idris example
||| span (/= 'C') "EFGH"
||| ```
export
span : (Char -> Bool) -> String -> (String, String)
span p xs
    = case span p (unpack xs) of
           (x, y) => (pack x, pack y)

||| Splits the string into a part before the predicate
||| returns True and the rest of the string.
|||
||| ```idris example
||| break (== 'C') "ABCD"
||| ```
||| ```idris example
||| break (== 'C') "EFGH"
||| ```
public export
break : (Char -> Bool) -> String -> (String, String)
break p = span (not . p)


||| Splits the string into parts with the predicate
||| indicating separator characters.
|||
||| ```idris example
||| split (== '.') ".AB.C..D"
||| ```
public export
split : (Char -> Bool) -> String -> List1 String
split p xs = map pack (split p (unpack xs))

export
stringToNatOrZ : String -> Nat
stringToNatOrZ = fromInteger . prim__cast_StringInteger

export
toUpper : String -> String
toUpper str = pack (map toUpper (unpack str))

export
toLower : String -> String
toLower str = pack (map toLower (unpack str))

export partial
strIndex : String -> Int -> Char
strIndex = prim__strIndex

export partial
strLength : String -> Int
strLength = prim__strLength

export partial
strSubstr : Int -> Int -> String -> String
strSubstr = prim__strSubstr

export partial
strTail : String -> String
strTail = prim__strTail

export
isPrefixOf : String -> String -> Bool
isPrefixOf a b = isPrefixOf (unpack a) (unpack b)

export
isSuffixOf : String -> String -> Bool
isSuffixOf a b = isSuffixOf (unpack a) (unpack b)

export
isInfixOf : String -> String -> Bool
isInfixOf a b = isInfixOf (unpack a) (unpack b)

parseNumWithoutSign : List Char -> Integer -> Maybe Integer
parseNumWithoutSign []        acc = Just acc
parseNumWithoutSign (c :: cs) acc =
  if (c >= '0' && c <= '9')
  then parseNumWithoutSign cs ((acc * 10) + (cast ((ord c) - (ord '0'))))
  else Nothing

||| Convert a positive number string to a Num.
|||
||| ```idris example
||| parsePositive "123"
||| ```
||| ```idris example
||| parsePositive {a=Int} " +123"
||| ```
public export
parsePositive : Num a => String -> Maybe a
parsePositive s = parsePosTrimmed (trim s)
  where
    parsePosTrimmed : String -> Maybe a
    parsePosTrimmed s with (strM s)
      parsePosTrimmed ""             | StrNil         = Nothing
      parsePosTrimmed (strCons '+' xs) | (StrCons '+' xs) =
        map fromInteger (parseNumWithoutSign (unpack xs) 0)
      parsePosTrimmed (strCons x xs) | (StrCons x xs) =
        if (x >= '0' && x <= '9')
        then  map fromInteger (parseNumWithoutSign (unpack xs)  (cast (ord x - ord '0')))
        else Nothing

||| Convert a number string to a Num.
|||
||| ```idris example
||| parseInteger " 123"
||| ```
||| ```idris example
||| parseInteger {a=Int} " -123"
||| ```
public export
parseInteger : Num a => Neg a => String -> Maybe a
parseInteger s = parseIntTrimmed (trim s)
  where
    parseIntTrimmed : String -> Maybe a
    parseIntTrimmed s with (strM s)
      parseIntTrimmed ""             | StrNil         = Nothing
      parseIntTrimmed (strCons x xs) | (StrCons x xs) =
        if (x == '-')
          then map (\y => negate (fromInteger y)) (parseNumWithoutSign (unpack xs) 0)
          else if (x == '+')
            then map fromInteger (parseNumWithoutSign (unpack xs) (cast {from=Int} 0))
            else if (x >= '0' && x <= '9')
            then map fromInteger (parseNumWithoutSign (unpack xs) (cast (ord x - ord '0')))
              else Nothing


||| Convert a number string to a Double.
|||
||| ```idris example
||| parseDouble "+123.123e-2"
||| ```
||| ```idris example
||| parseDouble {a=Int} " -123.123E+2"
||| ```
||| ```idris example
||| parseDouble {a=Int} " +123.123"
||| ```
export -- it's a bit too slow at compile time
covering
parseDouble : String -> Maybe Double
parseDouble = mkDouble . wfe . trim
  where
    intPow : Integer -> Integer -> Double
    intPow base exp = assert_total $ if exp > 0 then (num base exp) else 1 / (num base exp)
      where
        num : Integer -> Integer -> Double
        num base 0 = 1
        num base e = if e < 0
                     then cast base * num base (e + 1)
                     else cast base * num base (e - 1)

    natpow : Double -> Nat -> Double
    natpow x Z = 1
    natpow x (S n) = x * (natpow x n)

    mkDouble : Maybe (Double, Double, Integer) -> Maybe Double
    mkDouble (Just (w, f, e)) = let ex = intPow 10 e in
                                Just $ (w * ex + f * ex)
    mkDouble Nothing = Nothing

    wfe : String -> Maybe (Double, Double, Integer)
    wfe cs = case split (== '.') cs of
               (wholeAndExp ::: []) =>
                 case split (\c => c == 'e' || c == 'E') wholeAndExp of
                   (whole:::exp::[]) =>
                     do
                       w <- cast {from=Integer} <$> parseInteger whole
                       e <- parseInteger exp
                       pure (w, 0, e)
                   (whole:::[]) =>
                     do
                       w <- cast {from=Integer} <$> parseInteger whole
                       pure (w, 0, 0)
                   _ => Nothing
               (whole:::fracAndExp::[]) =>
                 case split (\c => c == 'e' || c == 'E') fracAndExp of
                   ("":::exp::[]) => Nothing
                   (frac:::exp::[]) =>
                     do
                       w <- cast {from=Integer} <$> parseInteger whole
                       f <- (/ (natpow 10 (length frac))) <$>
                            (cast <$> parseNumWithoutSign (unpack frac) 0)
                       e <- parseInteger exp
                       pure (w, if w < 0 then (-f) else f, e)
                   (frac:::[]) =>
                     do
                       w <- cast {from=Integer} <$> parseInteger whole
                       f <- (/ (natpow 10 (length frac))) <$>
                            (cast <$> parseNumWithoutSign (unpack frac) 0)
                       pure (w, if w < 0 then (-f) else f, 0)
                   _ => Nothing
               _ => Nothing

public export
null : String -> Bool
null = (== "")
