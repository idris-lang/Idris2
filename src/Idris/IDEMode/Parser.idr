||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Core.Core
import Core.FC

import Protocol.SExp
import Protocol.SExp.Parser

import Parser.Source

Cast SExpError Error where
  cast (LexError    err) = fromLexError                   (Virtual Interactive) err
  cast (ParseErrors err) = fromParsingErrors {ann = Void} (Virtual Interactive) err

export
covering
parseSExp : String -> Either Error SExp
parseSExp inp
    = mapFst cast $ Protocol.SExp.Parser.parseSExp inp
