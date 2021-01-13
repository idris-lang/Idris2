||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Idris.IDEMode.Commands

import Data.Maybe
import Data.List
import Data.Strings
import Parser.Lexer.Source
import Parser.Source
import Parser.Support
import Text.Lexer
import Text.Parser
import Utils.Either
import Utils.String

%default total

%hide Text.Lexer.symbols
%hide Parser.Lexer.Source.symbols

symbols : List String
symbols = ["(", ":", ")"]

ideTokens : TokenMap Token
ideTokens =
    map (\x => (exact x, Symbol)) symbols ++
    [(digits, \x => IntegerLit (cast x)),
     (stringLit, \x => StringLit (fromMaybe "" (escape (stripQuotes x)))),
     (identAllowDashes, \x => Ident x),
     (space, Comment)]

idelex : String -> Either (Int, Int, String) (List (WithBounds Token))
idelex str
    = case lex ideTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkBounded EndInput False l c l c])
           (_, fail) => Left fail
    where
      notComment : WithBounds Token -> Bool
      notComment t = case t.val of
                          Comment _ => False
                          _ => True

covering
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

ideParser : {e : _} -> String -> Grammar Token e ty -> Either (ParseError Token) ty
ideParser str p
    = do toks   <- mapError LexFail $ idelex str
         parsed <- mapError toGenericParsingError $ parse p toks
         Right (fst parsed)


export
covering
parseSExp : String -> Either (ParseError Token) SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
