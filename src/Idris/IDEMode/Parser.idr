||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Idris.IDEMode.Commands
import Core.Core
import Core.FC

import Data.List
import Parser.Lexer.Source
import Parser.Source
import Parser.Support
import Libraries.Text.Lexer
import Libraries.Text.Lexer.Tokenizer
import Libraries.Text.Parser

%default total

%hide Text.Lexer.symbols
%hide Parser.Lexer.Source.symbols

symbols : List String
symbols = ["(", ":", ")"]

stringTokens : Tokenizer Token
stringTokens
    = match (someUntil (is '"') (escape (is '\\') any <|> any)) $ StringLit 0

ideTokens : Tokenizer Token
ideTokens =
      match (choice $ exact <$> symbols) Symbol
  <|> match digits (IntegerLit . cast)
  <|> compose (is '"')
              (const $ StringBegin Single)
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
            String -> Grammar State Token e ty -> Either Error ty
ideParser str p
    = do toks   <- mapFst (fromLexError (Virtual Interactive)) $ idelex str
         (_, _, (parsed, _)) <- mapFst (fromParsingErrors (Virtual Interactive)) $ parseWith p toks
         Right parsed


export
covering
parseSExp : String -> Either Error SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
