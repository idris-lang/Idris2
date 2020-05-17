||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Idris.IDEMode.Commands

import Text.Parser
import Parser.Lexer
import Parser.Support
import Text.Lexer
import Utils.String

import Data.List
import Data.Strings

%hide Text.Lexer.symbols
%hide Parser.Lexer.symbols

symbols : List String
symbols = ["(", ":", ")"]

ideTokens : TokenMap Token
ideTokens =
    map (\x => (exact x, Symbol)) symbols ++
    [(digits, \x => Literal (cast x)),
     (stringLit, \x => StrLit (stripQuotes x)),
     (identAllowDashes, \x => NSIdent [x]),
     (space, Comment)]

idelex : String -> Either (Int, Int, String) (List (TokenData Token))
idelex str
    = case lex ideTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

sexp : Rule SExp
sexp
    = do symbol ":"; exactIdent "True"
         pure (BoolAtom True)
  <|> do symbol ":"; exactIdent "False"
         pure (BoolAtom False)
  <|> do i <- intLit
         pure (IntegerAtom i)
  <|> do str <- strLit
         pure (StringAtom str)
  <|> do symbol ":"; x <- unqualifiedName
         pure (SymbolAtom x)
  <|> do symbol "("
         xs <- many sexp
         symbol ")"
         pure (SExpList xs)

ideParser : {e : _} ->
            String -> Grammar (TokenData Token) e ty -> Either ParseError ty
ideParser str p
    = case idelex str of
           Left err => Left $ LexFail err
           Right toks =>
              case parse p toks of
                   Left (Error err []) =>
                          Left $ ParseFail err Nothing []
                   Left (Error err (t :: ts)) =>
                          Left $ ParseFail err (Just (line t, col t))
                                               (map tok (t :: ts))
                   Right (val, _) => Right val

export
parseSExp : String -> Either ParseError SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
