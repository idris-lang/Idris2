module Text.Lexer

import Data.Bool.Extra
import Data.List
import Data.Nat

import public Text.Lexer.Core
import public Text.Quantity
import public Text.Token

%default total

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
concat = Lexer.Core.concatMap id

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

||| Recognise a hexidecimal literal, prefixed by "0x" or "0X"
||| /0[Xx][0-9A-Fa-f]+/
export
hexLit : Lexer
hexLit = approx "0x" <+> hexDigits

||| Recognise an octal literal, prefixed by "0o"
||| /0[Xx][0-9A-Fa-f]+/
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
