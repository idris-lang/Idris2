module Protocol.SExp.Parser

import Idris.IDEMode.Commands

import Data.List

import Libraries.Text.Lexer
import Parser.Lexer.Common
import Parser.Source
import Parser.Lexer.Source
import Libraries.Text.Token
import Libraries.Text.Lexer.Tokenizer
import Libraries.Text.Parser

import Core.Metadata

%default total

%hide Text.Lexer.symbols
%hide Parser.Lexer.Source.symbols
%hide Parser.Rule.Source.symbol

symbols : List String
symbols = ["(", ":", ")"]

symbol : String -> Rule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Symbol s => guard (s == req)
                 _ => Nothing


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
  <|> do Parser.symbol "("
         xs <- Parser.many sexp
         symbol ")"
         pure (SExpList xs)

public export
data SExpError =
    LexError (StopReason, Int, Int, String)
  | ParseErrors (List1 $ ParsingError Token)

ideParser : {e : _} ->
            String -> Grammar ParsingState Token e ty -> Either SExpError ty
ideParser str p
    = do toks   <- mapFst LexError $ idelex str
         (_, _, (parsed, _)) <- mapFst ParseErrors $ parseWith p toks
         Right parsed

export
covering
parseSExp : String -> Either SExpError SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
