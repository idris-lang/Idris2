module Text.Lexer

import Data.Bool.Extra
import Data.List
import Data.Maybe
import Data.Nat
import Data.Strings

import public Control.Delayed
import public Text.Bounded
import public Text.Quantity
import public Text.Token

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

export
toTokenMap : List (Lexer, k) -> TokenMap (Token k)
toTokenMap = map $ \(l, kind) => (l, Tok kind)

||| Recognise any character.
||| /./
export
any : Lexer
any = pred (const True)

||| Recognise a lexer or recognise no input. This is not guaranteed
||| to consume input.
||| /`l`?/
export
opt : (l : Lexer) -> Recognise False
opt l = l <|> empty

||| Recognise any character if the sub-lexer `l` fails.
||| /(?!`l`)./
export
non : (l : Lexer) -> Lexer
non l = reject l <+> any

||| Produce recognisers by applying a function to elements of a container, and
||| recognise the first match. Consumes input if the function produces consuming
||| recognisers. Fails if the container is empty.
export
choiceMap : {c : Bool} ->
            Foldable t => (a -> Recognise c) -> t a -> Recognise c
choiceMap {c} f xs = foldr (\x, acc => rewrite sym (andSameNeutral c) in
                                               f x <|> acc)
                           fail xs

||| Recognise the first matching recogniser in a container. Consumes input if
||| recognisers in the list consume. Fails if the container is empty.
export
choice : {c : _} ->
         Foldable t => t (Recognise c) -> Recognise c
choice = choiceMap id

||| Sequence a list of recognisers. Guaranteed to consume input if the list is
||| non-empty and the recognisers consume.
export
concat : {c : _} ->
         (xs : List (Recognise c)) -> Recognise (isCons xs && c)
concat = concatMap id

||| Recognise a specific character.
||| /[`x`]/
export
is : (x : Char) -> Lexer
is x = pred (==x)

||| Recognise anything but the given character.
||| /[\^`x`]/
export
isNot : (x : Char) -> Lexer
isNot x = pred (/=x)

||| Recognise a specific character (case-insensitive).
||| /[`x`]/i
export
like : (x : Char) -> Lexer
like x = pred (\y => toUpper x == toUpper y)

||| Recognise anything but the given character (case-insensitive).
||| /[\^`x`]/i
export
notLike : (x : Char) -> Lexer
notLike x = pred (\y => toUpper x /= toUpper y)

||| Recognise a specific string.
||| Fails if the string is empty.
||| /`str`/
export
exact : (str : String) -> Lexer
exact str = case unpack str of
                 [] => fail
                 (x :: xs) => concatMap is (x :: xs)

||| Recognise a specific string (case-insensitive).
||| Fails if the string is empty.
||| /`str`/i
export
approx : (str : String) -> Lexer
approx str = case unpack str of
                  [] => fail
                  (x :: xs) => concatMap like (x :: xs)

||| Recognise any of the characters in the given string.
||| /[`chars`]/
export
oneOf : (chars : String) -> Lexer
oneOf chars = pred (\x => x `elem` unpack chars)

||| Recognise a character range. Also works in reverse!
||| /[`start`-`end`]/
export
range : (start : Char) -> (end : Char) -> Lexer
range start end = pred (\x => (x >= min start end)
                           && (x <= max start end))

mutual
  ||| Recognise a sequence of at least one sub-lexers
  ||| /`l`+/
  export
  some : Lexer -> Lexer
  some l = l <+> many l

  ||| Recognise a sequence of at zero or more sub-lexers. This is not
  ||| guaranteed to consume input
  ||| /`l`\*/
  export
  many : Lexer -> Recognise False
  many l = opt (some l)

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopBefore` is encountered. `stopBefore` will not be consumed.
||| Not guaranteed to consume input.
||| /((?!`stopBefore`)`l`)\*/
export
manyUntil : (stopBefore : Recognise c) -> (l : Lexer) -> Recognise False
manyUntil stopBefore l = many (reject stopBefore <+> l)

||| Repeat the sub-lexer `l` zero or more times until the lexer
||| `stopAfter` is encountered, and consume it. Guaranteed to
||| consume if `stopAfter` consumes.
||| /`l`\*?`stopAfter`/
export
manyThen : (stopAfter : Recognise c) -> (l : Lexer) -> Recognise c
manyThen stopAfter l = manyUntil stopAfter l <+> stopAfter

||| Recognise a sub-lexer repeated as specified by `q`. Fails if `q` has
||| `min` and `max` in the wrong order. Consumes input unless `min q` is zero.
||| /`l`{`q`}/
export
count : (q : Quantity) -> (l : Lexer) -> Recognise (isSucc (min q))
count (Qty Z Nothing) l = many l
count (Qty Z (Just Z)) _ = empty
count (Qty Z (Just (S max))) l = opt $ l <+> count (atMost max) l
count (Qty (S min) Nothing) l = l <+> count (atLeast min) l
count (Qty (S min) (Just Z)) _ = fail
count (Qty (S min) (Just (S max))) l = l <+> count (between min max) l

||| Recognise a single digit 0-9
||| /[0-9]/
export
digit : Lexer
digit = pred isDigit

||| Recognise one or more digits
||| /[0-9]+/
export
digits : Lexer
digits = some digit

||| Recognise a single binary digit
||| /[0-1]/
export
binDigit : Lexer
binDigit = pred (\c => c == '0' || c == '1')

||| Recognise one or more binary digits
||| /[0-1]+/
export
binDigits : Lexer
binDigits = some binDigit

||| Recognise a single hexidecimal digit
||| /[0-9A-Fa-f]/
export
hexDigit : Lexer
hexDigit = pred isHexDigit

||| Recognise one or more hexidecimal digits
||| /[0-9A-Fa-f]+/
export
hexDigits : Lexer
hexDigits = some hexDigit

||| Recognise a single octal digit
||| /[0-8]/
export
octDigit : Lexer
octDigit = pred isOctDigit

||| Recognise one or more octal digits
||| /[0-8]+/
export
octDigits : Lexer
octDigits = some octDigit

||| Recognise a single alpha character
||| /[A-Za-z]/
export
alpha : Lexer
alpha = pred isAlpha

||| Recognise one or more alpha characters
||| /[A-Za-z]+/
export
alphas : Lexer
alphas = some alpha

||| Recognise a lowercase alpha character
||| /[a-z]/
export
lower : Lexer
lower = pred isLower

||| Recognise one or more lowercase alpha characters
||| /[a-z]+/
export
lowers : Lexer
lowers = some lower

||| Recognise an uppercase alpha character
||| /[A-Z]/
export
upper : Lexer
upper = pred isUpper

||| Recognise one or more uppercase alpha characters
||| /[A-Z]+/
export
uppers : Lexer
uppers = some upper

||| Recognise an alphanumeric character
||| /[A-Za-z0-9]/
export
alphaNum : Lexer
alphaNum = pred isAlphaNum

||| Recognise one or more alphanumeric characters
||| /[A-Za-z0-9]+/
export
alphaNums : Lexer
alphaNums = some alphaNum

||| Recognise a single whitespace character
||| /\\s/
export
space : Lexer
space = pred isSpace

||| Recognise one or more whitespace characters
||| /\\s+/
export
spaces : Lexer
spaces = some space

||| Recognise a single newline sequence. Understands CRLF, CR, and LF
||| /\\r\\n|[\\r\\n]/
export
newline : Lexer
newline = let crlf = "\r\n" in
              exact crlf <|> oneOf crlf

||| Recognise one or more newline sequences. Understands CRLF, CR, and LF
||| /(\\r\\n|[\\r\\n])+)/
export
newlines : Lexer
newlines = some newline

||| Recognise a single non-whitespace, non-alphanumeric character
||| /[\^\\sA-Za-z0-9]/
export
symbol : Lexer
symbol = pred (\x => not (isSpace x || isAlphaNum x))

||| Recognise one or more non-whitespace, non-alphanumeric characters
||| /[\^\\sA-Za-z0-9]+/
export
symbols : Lexer
symbols = some symbol

||| Recognise a single control character
||| /[\\x00-\\x1f\\x7f-\\x9f]/
export
control : Lexer
control = pred isControl

||| Recognise one or more control characters
||| /[\\x00-\\x1f\\x7f-\\x9f]+/
export
controls : Lexer
controls = some control

||| Recognise zero or more occurrences of a sub-lexer between
||| delimiting lexers
||| /`start`(`l`)\*?`end`/
export
surround : (start : Lexer) -> (end : Lexer) -> (l : Lexer) -> Lexer
surround start end l = start <+> manyThen end l

||| Recognise zero or more occurrences of a sub-lexer surrounded
||| by the same quote lexer on both sides (useful for strings)
||| /`q`(`l`)\*?`q`/
export
quote : (q : Lexer) -> (l : Lexer) -> Lexer
quote q l = surround q q l

||| Recognise an escape character (often '\\') followed by a sub-lexer
||| /[`esc`]`l`/
export
escape : (esc : Char) -> Lexer -> Lexer
escape esc l = is esc <+> l

||| Recognise a string literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
||| /"(\\\\.|.)\*?"/
export
stringLit : Lexer
stringLit = quote (is '"') (escape '\\' any <|> any)

||| Recognise a character literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
||| /'(\\\\.|[\^'])'/
export
charLit : Lexer
charLit = let q = '\'' in
              is q <+> (escape '\\' (control <|> any) <|> isNot q) <+> is q
  where
    lexStr : List String -> Lexer
    lexStr [] = fail
    lexStr (t :: ts) = exact t <|> lexStr ts

    control : Lexer
    control = lexStr ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
                      "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
                      "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
                      "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US",
                      "SP",  "DEL"]
                <|> (is 'x' <+> hexDigits)
                <|> (is 'o' <+> octDigits)
                <|> digits

||| Recognise an integer literal (possibly with a '-' prefix)
||| /-?[0-9]+/
export
intLit : Lexer
intLit = opt (is '-') <+> digits

||| Recognise a binary literal, prefixed by "0b"
||| /0b[0-1]+/
export
binLit : Lexer
binLit = exact "0b" <+> binDigits

||| Recognise a hexidecimal literal, prefixed by "0x" or "0X"
||| /0[Xx][0-9A-Fa-f]+/
export
hexLit : Lexer
hexLit = approx "0x" <+> hexDigits

||| Recognise an octal literal, prefixed by "0o"
||| /0o[0-9A-Fa-f]+/
export
octLit : Lexer
octLit = exact "0o" <+> octDigits

||| Recognise `start`, then recognise all input until a newline is encountered,
||| and consume the newline. Will succeed if end-of-input is encountered before
||| a newline.
||| /`start`[\^\\r\\n]+(\\r\\n|[\\r\\n])?/
export
lineComment : (start : Lexer) -> Lexer
lineComment start = start <+> manyUntil newline any <+> opt newline

||| Recognise all input between `start` and `end` lexers.
||| Supports balanced nesting.
|||
||| For block comments that don't support nesting (such as C-style comments),
||| use `surround`
export
blockComment : (start : Lexer) -> (end : Lexer) -> Lexer
blockComment start end = start <+> middle <+> end
  where
    middle : Recognise False
    middle = manyUntil end (blockComment start end <|> any)
