module Language.JSON.Lexer

import Language.JSON.String
import Text.Lexer

import public Language.JSON.Tokens

%default total

private
numberLit : Lexer
numberLit
  = let sign  = is '-'
        whole = is '0' <|> range '1' '9' <+> many digit
        frac  = is '.' <+> digits
        exp   = like 'e' <+> opt (oneOf "+-") <+> digits in
        opt sign <+> whole <+> opt frac <+> opt exp

private
jsonTokenMap : TokenMap JSONToken
jsonTokenMap = toTokenMap $
  [ (spaces, JTIgnore)
  , (is ',', JTPunct Comma)
  , (is ':', JTPunct Colon)
  , (is '[', JTPunct $ Square Open)
  , (is ']', JTPunct $ Square Close)
  , (is '{', JTPunct $ Curly Open)
  , (is '}', JTPunct $ Curly Close)
  , (exact "null", JTNull)
  , (exact strTrue <|> exact strFalse, JTBoolean)
  , (numberLit, JTNumber)
  , (permissiveStringLit, JTString)
  ]

export
lexJSON : String -> Maybe (List (WithBounds JSONToken))
lexJSON str
  = case lex jsonTokenMap str of
         (tokens, _, _, "") => Just $ tokens
         _ => Nothing
