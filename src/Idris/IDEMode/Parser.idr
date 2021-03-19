||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Idris.IDEMode.Commands
import Core.Core

import Data.Maybe
import Data.List
import Data.Strings
import Parser.Lexer.Source
import Parser.Source
import Parser.Support
import Libraries.Text.Lexer
import Libraries.Text.Lexer.Tokenizer
import Libraries.Text.Parser
import Libraries.Utils.Either
import Libraries.Utils.String

%default total

%hide Text.Lexer.symbols
%hide Parser.Lexer.Source.symbols

symbols : List String
symbols = ["(", ":", ")"]

stringTokens : Tokenizer Token
stringTokens
    = match (someUntil (is '"') (escape (is '\\') any <|> any)) (\x => StringLit 0 x)

ideTokens : Tokenizer Token
ideTokens =
      match (choice $ exact <$> symbols) Symbol
  <|> match digits (\x => IntegerLit (cast x))
  <|> compose (is '"')
              (const $ StringBegin False)
              (const ())
              (const stringTokens)
              (const $ is '"')
              (const StringEnd)
  <|> match identAllowDashes Ident
  <|> match space (const Comment)

idelex : String -> Either (StopReason, Int, Int, String) (List (WithBounds Token))
idelex str
    = case lex ideTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (EndInput, l, c, _)) => Right (filter notComment tok ++
                                               [MkBounded EndInput False (MkBounds l c l c)])
           (_, fail) => Left fail
    where
      notComment : WithBounds Token -> Bool
      notComment t = case t.val of
                          Comment => False
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
  <|> do str <- simpleStr
         pure (StringAtom str)
  <|> do symbol ":"; x <- unqualifiedName
         pure (SymbolAtom x)
  <|> do symbol "("
         xs <- many sexp
         symbol ")"
         pure (SExpList xs)

ideParser : {e : _} ->
            (fname : String) -> String -> Grammar Token e ty -> Either Error ty
ideParser fname str p
    = do toks   <- mapError (fromLexError fname) $ idelex str
         parsed <- mapError (fromParsingError fname) $ parse p toks
         Right (fst parsed)


export
covering
parseSExp : String -> Either Error SExp
parseSExp inp
    = ideParser "(interactive)" inp (do c <- sexp; eoi; pure c)
