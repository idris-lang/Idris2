module Language.JSON.String.Tokens

import Data.List
import Data.String
import Data.String.Extra
import Text.Token

%default total

public export
data JSONStringTokenKind
  = JSTQuote
  | JSTChar
  | JSTSimpleEscape
  | JSTUnicodeEscape

public export
JSONStringToken : Type
JSONStringToken = Token JSONStringTokenKind

public export
Eq JSONStringTokenKind where
  (==) JSTQuote JSTQuote = True
  (==) JSTChar JSTChar = True
  (==) JSTSimpleEscape JSTSimpleEscape = True
  (==) JSTUnicodeEscape JSTUnicodeEscape = True
  (==) _ _ = False

private
charValue : String -> Char
charValue x = case index 0 x of
                   Nothing => '\NUL'
                   Just c  => c

private
simpleEscapeValue : String -> Char
simpleEscapeValue x
  = case index 1 x of
         Nothing => '\NUL'
         Just c => case c of
                        '"'  => '"'
                        '\\' => '\\'
                        '/'  => '/'
                        'b'  => '\b'
                        'f'  => '\f'
                        'n'  => '\n'
                        'r'  => '\r'
                        't'  => '\t'
                        _    => '\NUL'

private
unicodeEscapeValue : String -> Char
unicodeEscapeValue x = fromHex (drop 2 $ fastUnpack x) 0
  where hexVal : Char -> Int
        hexVal c = if c >= 'A'
                      then ord c - ord 'A' + 10
                      else ord c - ord '0'

        fromHex : List Char -> Int -> Char
        fromHex       [] acc = chr acc
        fromHex (h :: t) acc = fromHex t (hexVal h + 16 * acc)

public export
TokenKind JSONStringTokenKind where
  TokType JSTQuote = ()
  TokType JSTChar = Char
  TokType JSTSimpleEscape = Char
  TokType JSTUnicodeEscape = Char

  tokValue JSTQuote = const ()
  tokValue JSTChar = charValue
  tokValue JSTSimpleEscape = simpleEscapeValue
  tokValue JSTUnicodeEscape = unicodeEscapeValue
