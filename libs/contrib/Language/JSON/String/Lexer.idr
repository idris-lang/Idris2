module Language.JSON.String.Lexer

import Data.Nat
import Language.JSON.String.Tokens
import Text.Lexer

%default total

export
quo : Lexer
quo = is '"'

export
esc : Lexer -> Lexer
esc = escape (is '\\')

private
unicodeEscape : Lexer
unicodeEscape = esc $ is 'u' <+> count (exactly 4) hexDigit

private
simpleEscape : Lexer
simpleEscape = esc $ oneOf "\"\\/bfnrt"

private
legalChar : Lexer
legalChar = non (quo <|> is '\\' <|> control)

private
jsonStringTokenMap : TokenMap JSONStringToken
jsonStringTokenMap = toTokenMap $
  [ (quo, JSTQuote)
  , (unicodeEscape, JSTUnicodeEscape)
  , (simpleEscape, JSTSimpleEscape)
  , (legalChar, JSTChar)
  ]

export
lexString : String -> Maybe (List (WithBounds JSONStringToken))
lexString x = case lex jsonStringTokenMap x of
                   (toks, _, _, "") => Just $ toks
                   _ => Nothing
