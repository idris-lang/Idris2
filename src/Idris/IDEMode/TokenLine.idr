||| Tokenise a source line for easier processing
module Idris.IDEMode.TokenLine

import Parser.Lexer.Source
import Libraries.Text.Lexer

%default total

public export
RawName : Type
RawName = String

public export
data SourcePart
  = Whitespace String
  | Name RawName
  | HoleName String
  | LBrace
  | RBrace
  | Equal
  | AsPattern
  | Other String

------------------------------------------------------------------------
-- Printer
------------------------------------------------------------------------

export
toString : SourcePart -> String
toString (Whitespace str) = str
toString (Name n) = n
toString (HoleName n) = "?" ++ n
toString LBrace = "{"
toString RBrace = "}"
toString Equal = "="
toString AsPattern = "@"
toString (Other str) = str

------------------------------------------------------------------------
-- Parser
------------------------------------------------------------------------

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
     (is '@', const AsPattern),
     (any, Other)]

export
tokens : String -> List SourcePart
tokens str
    = case lex srcTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (srctoks, (l, c, rest)) =>
              map val srctoks ++ (if rest == "" then [] else [Other rest])
