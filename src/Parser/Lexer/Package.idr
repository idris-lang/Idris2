module Parser.Lexer.Package

import public Parser.Lexer.Common
import public Text.Lexer
import public Text.Parser
import public Text.Bounded
import Text.PrettyPrint.Prettyprinter

import Data.List
import Data.List1
import Data.Strings
import Data.String.Extra
import Utils.String

%default total

public export
data Token
  = Comment String
  | EndOfInput
  | Equals
  | DotSepIdent (List1 String)
  | Separator
  | Space
  | StringLit String

public export
Show Token where
  show (Comment str) = "Comment: " ++ str
  show EndOfInput = "EndOfInput"
  show Equals = "Equals"
  show (DotSepIdent dsid) = "DotSepIdentifier: " ++ dotSep (List1.toList dsid)
  show Separator = "Separator"
  show Space = "Space"
  show (StringLit s) = "StringLit: " ++ s

public export
Pretty Token where
  pretty (Comment str) = "Comment:" <++> pretty str
  pretty EndOfInput = "EndOfInput"
  pretty Equals = "Equals"
  pretty (DotSepIdent dsid) = "DotSepIdentifier:" <++> concatWith (surround dot) (pretty <$> List1.toList dsid)
  pretty Separator = "Separator"
  pretty Space = "Space"
  pretty (StringLit s) = "StringLit:" <++> pretty s

equals : Lexer
equals = is '='

separator : Lexer
separator = is ','

rawTokens : TokenMap Token
rawTokens =
  [ (equals, const Equals)
  , (comment, Comment . drop 2)
  , (namespacedIdent, DotSepIdent . splitNamespace)
  , (identAllowDashes, DotSepIdent . pure)
  , (separator, const Separator)
  , (spacesOrNewlines, const Space)
  , (stringLit, \s => StringLit (stripQuotes s))
  ]
  where
    splitNamespace : String -> List1 String
    splitNamespace = Data.Strings.split (== '.')

export
lex : String -> Either (Int, Int, String) (List (WithBounds Token))
lex str =
  case lexTo (const False) rawTokens str of
       (tokenData, (l, c, "")) =>
         Right $ (filter (useful . val) tokenData) ++ [MkBounded EndOfInput False l c l c]
       (_, fail) => Left fail
  where
    useful : Token -> Bool
    useful (Comment c) = False
    useful Space       = False
    useful _ = True
