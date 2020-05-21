||| Tokenise a source line for easier processing
module Idris.IDEMode.TokenLine

import Parser.Lexer.Source
import Text.Lexer

public export
data SourcePart
  = Whitespace String
  | Name String
  | HoleName String
  | LBrace
  | RBrace
  | Equal
  | Other String

holeIdent : Lexer
holeIdent = is '?' <+> identNormal

srcTokens : TokenMap SourcePart
srcTokens =
    [(identNormal, Name),
     (holeIdent, \x => HoleName (assert_total (prim__strTail x))),
     (space, Whitespace),
     (is '{', const LBrace),
     (is '}', const RBrace),
     (is '=', const Equal),
     (any, Other)]

export
tokens : String -> List SourcePart
tokens str
    = case lex srcTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (srctoks, (l, c, rest)) =>
              map tok srctoks ++ (if rest == "" then [] else [Other rest])
