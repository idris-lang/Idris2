module Protocol.SExp.Parser

import Protocol.SExp

import Parser.Lexer.Common
import Libraries.Text.Token
import Libraries.Text.Lexer.Tokenizer
import Libraries.Text.Parser
import Libraries.Text.PrettyPrint.Prettyprinter.Symbols
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Text.PrettyPrint.Prettyprinter.Doc

import Parser.Support.Escaping

%default total

{- To decouple parsing of S-expressions, we reproduce some
   functionality from the source-file parser. We duplicate it since we
   don't need the full blown functionality of the source-code token.
-}

public export
data SExpToken
  = StringLit String
  | IntegerLit Integer
  | Symbol String
  | Ident String
  | StringBegin Nat
  | StringEnd
  | Whitespace
  | EndInput

export
Show SExpToken where
  -- Literals
  show (IntegerLit x) = "literal " ++ show x
  -- String
  show (StringBegin hashtag) = "string begin"
  show StringEnd = "string end"
  show (StringLit x) = "string " ++ show x
  -- Identifiers
  show (Ident x) = "identifier " ++ x
  show (Symbol x) = "symbol " ++ x
  show Whitespace = " "
  show EndInput = "end of input"

export
Pretty Void SExpToken where
  -- Literals
  pretty (IntegerLit x) = pretty "literal" <++> pretty (show x)
  -- String
  pretty (StringBegin hashtag) = reflow "string begin"
  pretty StringEnd = reflow "string end"
  pretty (StringLit x) = pretty "string" <++> dquotes (pretty x)
  -- Identifiers
  pretty (Ident x) = pretty "identifier" <++> pretty x
  pretty (Symbol x) = pretty "symbol" <++> pretty x
  -- Special
  pretty Whitespace = pretty "space"
  pretty EndInput = reflow "end of input"

SExpRule : Type -> Type
SExpRule = Grammar () SExpToken True

EmptySExpRule : Type -> Type
EmptySExpRule = Grammar () SExpToken False

symbols : List String
symbols = ["(", ":", ")"]

symbol : String -> SExpRule ()
symbol req
    = terminal ("Expected '" ++ req ++ "'") $
               \case
                 Symbol s => guard (s == req)
                 _ => Nothing

space : SExpRule ()
space = terminal ("Expected a space") $
               \case
                 Whitespace => Just ()
                 _ => Nothing

exactIdent : String -> SExpRule ()
exactIdent req
    = terminal ("Expected " ++ req) $
               \case
                 Ident s => guard (s == req)
                 _ => Nothing

simpleStrLit : SExpRule String
simpleStrLit
    = terminal "Expected string literal" $
               \case
                 StringLit s => unescape 0 s
                 _ => Nothing

strBegin : SExpRule Nat
strBegin = terminal "Expected string begin" $
                    \case
                      StringBegin hashtag => Just hashtag
                      _ => Nothing

strEnd : SExpRule ()
strEnd = terminal "Expected string end" $
                  \case
                    StringEnd => Just ()
                    _ => Nothing

simpleStr : SExpRule String
simpleStr = strBegin *> commit *> (option "" simpleStrLit) <* strEnd

stringTokens : Tokenizer SExpToken
stringTokens
    = match (someUntil (is '"') (escape (is '\\') any <|> any)) StringLit

ideTokens : Tokenizer SExpToken
ideTokens =
      match (choice $ exact <$> symbols) Symbol
  <|> match digits (IntegerLit . cast)
  <|> compose (is '"')
              (const $ StringBegin 0)
              (const ())
              (const stringTokens)
              (const $ is '"')
              (const StringEnd)
  <|> match (some $ pred isSpace) (const Whitespace)
  <|> match identAllowDashes Ident

notWhitespace : WithBounds SExpToken -> Bool
notWhitespace btok = case btok.val of
  Whitespace => False
  _ => True

idelex : String ->
  Either (StopReason, Int, Int, String)
         (List (WithBounds SExpToken))
idelex str = case lex ideTokens str of
  -- Add the EndInput token so that we'll have a line and column
  -- number to read when storing spans in the file
  (tok, (EndInput, l, c, _)) => Right (filter notWhitespace tok ++
                                      [MkBounded EndInput False (MkBounds l c l c)])
  (_, fail) => Left fail


identifierSExp : SExpRule String
identifierSExp
    = terminal "Expected name" $
               \case
                 Ident str => Just str
                 _ => Nothing

intLit : SExpRule Integer
intLit
    = terminal "Expected integer literal" $
               \case
                 IntegerLit i => Just i
                 _ => Nothing


eoi : EmptySExpRule ()
eoi = ignore $ nextIs "Expected end of input" isEOI
  where
    isEOI : SExpToken -> Bool
    isEOI EndInput = True
    isEOI _ = False

covering
sexp : SExpRule SExp
sexp
    = do symbol ":"; exactIdent "True"
         pure (BoolAtom True)
  <|> do symbol ":"; exactIdent "False"
         pure (BoolAtom False)
  <|> do i <- intLit
         pure (IntegerAtom i)
  <|> do str <- simpleStr
         pure (StringAtom str)
  <|> do symbol ":"; x <- identifierSExp
         pure (SymbolAtom x)
  <|> do Parser.symbol "("
         xs <- many sexp
         symbol ")"
         pure (SExpList xs)

public export
data SExpError =
    LexError (StopReason, Int, Int, String)
  | ParseErrors (List1 $ ParsingError SExpToken)

ideParser : {e : _} ->
            String -> Grammar () SExpToken e ty -> Either SExpError ty
ideParser str p
    = do toks   <- mapFst LexError $ idelex str
         (_, _, (parsed, _)) <- mapFst ParseErrors $ parseWith p toks
         Right parsed

export
covering
parseSExp : String -> Either SExpError SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
