module Text.Lexer.Core

import public Control.Delayed
import Data.Bool.Extra
import Data.List
import Data.Maybe
import Data.Nat
import Data.Strings
import public Text.Bounded

%default total

||| A language of token recognisers.
||| @ consumes If `True`, this recogniser is guaranteed to consume at
|||            least one character of input when it succeeds.
export
data Recognise : (consumes : Bool) -> Type where
     Empty : Recognise False
     Fail : Recognise c
     Lookahead : (positive : Bool) -> Recognise c -> Recognise False
     Pred : (Char -> Bool) -> Recognise True
     SeqEat : Recognise True -> Inf (Recognise e) -> Recognise True
     SeqEmpty : Recognise e1 -> Recognise e2 -> Recognise (e1 || e2)
     SeqSame : Recognise e -> Recognise e -> Recognise e
     Alt : Recognise e1 -> Recognise e2 -> Recognise (e1 && e2)

||| A token recogniser. Guaranteed to consume at least one character.
public export
Lexer : Type
Lexer = Recognise True

||| Sequence two recognisers. If either consumes a character, the sequence
||| is guaranteed to consume a character.
export %inline
(<+>) : {c1 : Bool} ->
        Recognise c1 -> inf c1 (Recognise c2) -> Recognise (c1 || c2)
(<+>) {c1 = False} = SeqEmpty
(<+>) {c1 = True} = SeqEat

||| Alternative recognisers. If both consume, the combination is guaranteed
||| to consume a character.
export
(<|>) : Recognise c1 -> Recognise c2 -> Recognise (c1 && c2)
(<|>) = Alt

||| A recogniser that always fails.
export
fail : Recognise c
fail = Fail

||| Recognise no input (doesn't consume any input)
export
empty : Recognise False
empty = Empty

||| Recognise a character that matches a predicate
export
pred : (Char -> Bool) -> Lexer
pred = Pred

||| Positive lookahead. Never consumes input.
export
expect : Recognise c -> Recognise False
expect = Lookahead True

||| Negative lookahead. Never consumes input.
export
reject : Recognise c -> Recognise False
reject = Lookahead False

||| Sequence the recognisers resulting from applying a function to each element
||| of a list. The resulting recogniser will consume input if the produced
||| recognisers consume and the list is non-empty.
export
concatMap : (a -> Recognise c) -> (xs : List a) -> Recognise (isCons xs && c)
concatMap _ []                 = Empty
concatMap f (x :: [])          = f x
concatMap f (x :: xs@(_ :: _)) = SeqSame (f x) (concatMap f xs)

data StrLen : Type where
     MkStrLen : String -> Nat -> StrLen

getString : StrLen -> String
getString (MkStrLen str n) = str

strIndex : StrLen -> Nat -> Maybe Char
strIndex (MkStrLen str len) i
    = if cast {to = Integer} i >= cast len then Nothing
      else Just (assert_total (prim__strIndex str (cast i)))

mkStr : String -> StrLen
mkStr str = MkStrLen str (length str)

strTail : Nat -> StrLen -> StrLen
strTail start (MkStrLen str len)
    = MkStrLen (substr start len str) (minus len start)

-- If the string is recognised, returns the index at which the token
-- ends
scan : Recognise c -> List Char -> List Char -> Maybe (List Char, List Char)
scan Empty tok str = pure (tok, str)
scan Fail tok str = Nothing
scan (Lookahead positive r) tok str
    = if isJust (scan r tok str) == positive
         then pure (tok, str)
         else Nothing
scan (Pred f) tok [] = Nothing
scan (Pred f) tok (c :: str)
    = if f c
         then Just (c :: tok, str)
         else Nothing
scan (SeqEat r1 r2) tok str
    = do (tok', rest) <- scan r1 tok str
         -- TODO: Can we prove totality instead by showing idx has increased?
         assert_total (scan r2 tok' rest)
scan (SeqEmpty r1 r2) tok str
    = do (tok', rest) <- scan r1 tok str
         scan r2 tok' rest
scan (SeqSame r1 r2) tok str
    = do (tok', rest) <- scan r1 tok str
         scan r2 tok' rest
scan (Alt r1 r2) tok str
    = maybe (scan r2 tok str) Just (scan r1 tok str)

||| A mapping from lexers to the tokens they produce.
||| This is a list of pairs `(Lexer, String -> tokenType)`
||| For each Lexer in the list, if a substring in the input matches, run
||| the associated function to produce a token of type `tokenType`
public export
TokenMap : (tokenType : Type) -> Type
TokenMap tokenType = List (Lexer, String -> tokenType)

tokenise : (WithBounds a -> Bool) ->
           (line : Int) -> (col : Int) ->
           List (WithBounds a) -> TokenMap a ->
           List Char -> (List (WithBounds a), (Int, Int, List Char))
tokenise pred line col acc tmap str
    = case getFirstToken tmap str of
           Just (tok, line', col', rest) =>
           -- assert total because getFirstToken must consume something
               if pred tok
                  then (reverse acc, (line, col, []))
                  else assert_total (tokenise pred line' col' (tok :: acc) tmap rest)
           Nothing => (reverse acc, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : List Char -> Int -> Int
    getCols x c
         = case span (/= '\n') (reverse x) of
                (incol, []) => c + cast (length incol)
                (incol, _) => cast (length incol)

    getFirstToken : TokenMap a -> List Char ->
                    Maybe (WithBounds a, Int, Int, List Char)
    getFirstToken [] str = Nothing
    getFirstToken ((lex, fn) :: ts) str
        = case scan lex [] str of
               Just (tok, rest) =>
                 let line' = line + cast (countNLs tok)
                     col' = getCols tok col in
                     Just (MkBounded (fn (fastPack (reverse tok))) False line col line' col',
                           line', col', rest)
               Nothing => getFirstToken ts str

||| Given a mapping from lexers to token generating functions (the
||| TokenMap a) and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the
||| string where there are no recognised tokens.
export
lex : TokenMap a -> String -> (List (WithBounds a), (Int, Int, String))
lex tmap str
    = let (ts, (l, c, str')) = tokenise (const False) 0 0 [] tmap (fastUnpack str) in
          (ts, (l, c, fastPack str'))

export
lexTo : (WithBounds a -> Bool) ->
        TokenMap a -> String -> (List (WithBounds a), (Int, Int, String))
lexTo pred tmap str
    = let (ts, (l, c, str')) = tokenise pred 0 0 [] tmap (fastUnpack str) in
          (ts, (l, c, fastPack str'))
