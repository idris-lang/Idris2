module Data.Strings

import Data.List
import Data.List1

export
singleton : Char -> String
singleton c = strCons c ""

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 _ [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

partial
foldl1 : (a -> a -> a) -> List a -> a
foldl1 f (x::xs) = foldl f x xs

-- This function runs fast when compiled but won't compute at compile time.
-- If you need to unpack strings at compile time, use Prelude.unpack.
%foreign
  "scheme:string-unpack"
export
fastUnpack : String -> List Char

-- This works quickly because when string-concat builds the result, it allocates
-- enough room in advance so there's only one allocation, rather than lots!
--
-- Like fastUnpack, this function won't reduce at compile time.
-- If you need to concatenate strings at compile time, use Prelude.concat.
%foreign
  "scheme:string-concat"
  "javascript:lambda:(xs)=>''.concat(...__prim_idris2js_array(xs))"
export
fastConcat : List String -> String

-- This is a deprecated alias for fastConcat for backwards compatibility
-- (unfortunately, we don't have %deprecated yet).
export
fastAppend : List String -> String
fastAppend = fastConcat

||| Splits a character list into a list of whitespace separated character lists.
|||
||| ```idris example
||| words' (unpack " A B C  D E   ")
||| ```
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
lines' : List Char -> List (List Char)
lines' [] = []
lines' s  = case break isNL s of
              (l, s') => l :: case s' of
                                []       => []
                                _ :: s'' => lines' (assert_smaller s s'')

||| Splits a string into a list of newline separated strings.
|||
||| ```idris example
||| lines  "\rA BC\nD\r\nE\n"
||| ```
export
lines : String -> List String
lines s = map pack (lines' (unpack s))

||| Joins the character lists by newlines into a single character list.
|||
||| ```idris example
||| unlines' [['l','i','n','e'], ['l','i','n','e','2'], ['l','n','3'], ['D']]
||| ```
unlines' : List (List Char) -> List Char
unlines' [] = []
unlines' (l::ls) = l ++ '\n' :: unlines' ls

||| Joins the strings by newlines into a single string.
|||
||| ```idris example
||| unlines ["line", "line2", "ln3", "D"]
||| ```
export
unlines : List String -> String
unlines = pack . unlines' . map unpack

export
ltrim : String -> String
ltrim xs = pack (ltrimChars (unpack xs))
  where
    ltrimChars : List Char -> List Char
    ltrimChars [] = []
    ltrimChars (x :: xs) = if isSpace x then ltrimChars xs else (x :: xs)

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

public export
data StrM : String -> Type where
    StrNil : StrM ""
    StrCons : (x : Char) -> (xs : String) -> StrM (strCons x xs)

public export -- primitives, so assert_total and believe_me needed
strM : (x : String) -> StrM x
strM "" = StrNil
strM x
    = assert_total $ believe_me $
        StrCons (prim__strHead x) (prim__strTail x)

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
parseInteger : (Num a, Neg a) => String -> Maybe a
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
