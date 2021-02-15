||| A small library introducing string positions
||| This can be used as an alternative to unpacking a string into a list of
||| characters
module Data.String.Position

import Data.String

%default total

||| @ValidPosition points to an existing character into
||| @str  its parameter string
||| Do NOT publicly export so that users cannot manufacture arbitrary positions
export
record ValidPosition (str : String) where
  constructor MkValidPosition
  ||| @currentIndex is the valid position into str
  currentIndex    : Int
  ||| @parameterLength is the length of the parameter str
  parameterLength : Int
-- TODO: add invariants?
--  0 isLength : length str === parameterLength
--  0 isIndex  : (0 `LTE` currentIndex, 0 `LT` parameterLength)

||| A position is either a ValidPosition or the end of the string
public export
Position : String -> Type
Position str = Maybe (ValidPosition str)

||| Manufacture a position by checking it is strictly inside the string
export
mkPosition : (str : String) -> Int -> Position str
mkPosition str idx
  = do let len : Int = cast (length str)
       guard (0 <= idx && idx < len)
       pure (MkValidPosition idx len)

||| Move a position (note that we do not need access to the string here)
export
mvPosition : ValidPosition str -> Int -> Position str
mvPosition (MkValidPosition pos len) idx
  = do guard (0 <= idx && idx < len)
       pure (MkValidPosition idx len)

||| Find the initial position inside the input string
export
init : (str : String) -> Position str
init str = mkPosition str 0

||| Move from a valid position to the next position in the string
export
next : ValidPosition str -> Position str
next (MkValidPosition pos len)
  = do let idx = pos + 1
       guard (idx < len)
       pure (MkValidPosition idx len)

||| We can safely access the character at a valid position
export
index : {str : _} -> ValidPosition str -> Char
index pos = assert_total (strIndex str pos.currentIndex)

||| We can successfully uncons the substring starting at a `ValidPosition`.
||| Note that we can use `map uncons pos` to uncons the substring starting
||| a `Position`.
export
uncons : {str : _} -> ValidPosition str -> (Char, Position str)
uncons pos = (index pos, next pos)

||| @span keeps munching characters of the substring starting at a given
||| position as long as the predicate is true of them. It returns the position
||| after the last successful munch.
||| Using `subString` to recover the string selected by `span` should yield
||| the same result as Data.String's `span`. That is to say we should have:
||| ```
||| subString pos (Position.span p pos) = String.span p (subString pos Nothing)
||| ```
export
span : {str : _} -> (Char -> Bool) -> Position str -> Position str
span p pos = do (c, str) <- map uncons pos
                if p c then assert_total (span p str) else pos

||| @count computes the length of the substring one would obtain if one were
||| to filter out characters based on the predicate passed as an argument.
||| It replaces the `length (filter p (fastUnpack str))` pattern.
export
count : {str : _} -> (Char -> Bool) -> Position str -> Nat
count p Nothing = 0
count p (Just pos) =
  if p (index pos)
    then S (assert_total (count p (next pos)))
    else assert_total (count p (next pos))

||| Distance between a starting position and an end one.
||| We assume that the end position is *after* the starting one, otherwise the
||| output may be negative.
export
distance : (start : Position str) ->
           (end : Position str) -> Int
distance Nothing _ = 0
distance (Just pos) pos' =
  let start = pos.currentIndex
      end = maybe pos.parameterLength currentIndex pos'
  in end - start

||| the substring of length `distance start end` that is contained between
||| start (inclusive) and end (exclusive).
export
subString : {str : _} ->
            (start : Position str) ->
            (end : Position str) -> String
subString Nothing pos' = ""
subString (Just pos) pos' =
  let start = pos.currentIndex
      end = maybe pos.parameterLength currentIndex pos'
  in assert_total (strSubstr start (end - start) str)
