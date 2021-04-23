module Parser.Lexer.Package

import public Parser.Lexer.Common
import public Libraries.Text.Lexer
import public Libraries.Text.Parser
import public Libraries.Text.Bounded
import Libraries.Text.PrettyPrint.Prettyprinter

import Data.List
import Data.List1
import Data.Strings
import Libraries.Data.String.Extra
import Libraries.Utils.String

import Core.Name.Namespace

%default total

public export
data Token
  = Comment String
  | EndOfInput
  | Equals
  | DotSepIdent (Maybe Namespace) String
  | Separator
  | Dot
  | LTE
  | GTE
  | LT
  | GT
  | EqOp
  | AndOp
  | Space
  | StringLit String
  | IntegerLit Integer

public export
Show Token where
  show (Comment str) = "Comment: " ++ str
  show EndOfInput = "EndOfInput"
  show Equals = "Equals"
  show (DotSepIdent ns n) = "DotSepIdentifier: " ++ show ns ++ "." ++ show n
  show Separator = "Separator"
  show Dot = "Dot"
  show LTE = "LTE"
  show GTE = "GTE"
  show LT = "LT"
  show GT = "GT"
  show EqOp = "EqOp"
  show AndOp = "AndOp"
  show Space = "Space"
  show (StringLit s) = "StringLit: " ++ s
  show (IntegerLit i) = "IntegerLit: " ++ show i

public export
Pretty Token where
  pretty (Comment str) = "Comment:" <++> pretty str
  pretty EndOfInput = "EndOfInput"
  pretty Equals = "Equals"
  pretty (DotSepIdent ns n) = "DotSepIdentifier:" <++> pretty ns <+> dot <+> pretty n
  pretty Separator = "Separator"
  pretty Dot = "Dot"
  pretty LTE = "LTE"
  pretty GTE = "GTE"
  pretty LT = "LT"
  pretty GT = "GT"
  pretty EqOp = "EqOp"
  pretty AndOp = "AndOp"
  pretty Space = "Space"
  pretty (StringLit s) = "StringLit:" <++> pretty s
  pretty (IntegerLit i) = "IntegerLit:" <++> pretty i

equals : Lexer
equals = is '='

separator : Lexer
separator = is ','

dot : Lexer
dot = is '.'

lte : Lexer
lte = is '<' <+> is '='

gte : Lexer
gte = is '>' <+> is '='

lt : Lexer
lt = is '<'

gt : Lexer
gt = is '>'

eqop : Lexer
eqop = is '=' <+> is '='

andop : Lexer
andop = is '&' <+> is '&'

rawTokens : TokenMap Token
rawTokens =
  [ (comment, Comment . drop 2)
  , (namespacedIdent, uncurry DotSepIdent . mkNamespacedIdent)
  , (identAllowDashes, DotSepIdent Nothing)
  , (separator, const Separator)
  , (dot, const Dot)
  , (lte, const LTE)
  , (gte, const GTE)
  , (lt, const LT)
  , (gt, const GT)
  , (eqop, const EqOp)
  , (andop, const AndOp)
  , (equals, const Equals)
  , (spacesOrNewlines, const Space)
  , (stringLit, \s => StringLit (stripQuotes s))
  , (intLit, \i => IntegerLit (cast i))
  ]

export
lex : String -> Either (Int, Int, String) (List (WithBounds Token))
lex str =
  case lexTo (const False) rawTokens str of
       (tokenData, (l, c, "")) =>
         Right $ (filter (useful . val) tokenData)
          ++ [MkBounded EndOfInput False (MkBounds l c l c)]
       (_, fail) => Left fail
  where
    useful : Token -> Bool
    useful (Comment c) = False
    useful Space       = False
    useful _ = True
