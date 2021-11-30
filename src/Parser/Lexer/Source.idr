module Parser.Lexer.Source

import public Parser.Lexer.Common

import Data.Either
import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.String.Extra
import public Libraries.Text.Bounded
import Libraries.Text.Lexer.Tokenizer
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

import Libraries.Utils.Hex
import Libraries.Utils.Octal
import Libraries.Utils.String

import Core.Name

%default total

public export
data IsMultiline = Multi | Single

public export
data Token
  -- Literals
  = CharLit String
  | DoubleLit Double
  | IntegerLit Integer
  -- String
  | StringBegin IsMultiline -- Whether is multiline string
  | StringEnd
  | InterpBegin
  | InterpEnd
  | StringLit Nat String
  -- Identifiers
  | HoleIdent String
  | Ident String
  | DotSepIdent Namespace String -- ident.ident
  | DotIdent String               -- .ident
  | Symbol String
  -- Whitespace
  | Space
  -- Comments
  | Comment
  | DocComment String
  -- Special
  | CGDirective String
  | EndInput
  | Keyword String
  | Pragma String
  | Unrecognised String

export
Show Token where
  -- Literals
  show (CharLit x) = "character " ++ show x
  show (DoubleLit x) = "double " ++ show x
  show (IntegerLit x) = "literal " ++ show x
  -- String
  show (StringBegin Single) = "string begin"
  show (StringBegin Multi) = "multiline string begin"
  show StringEnd = "string end"
  show InterpBegin = "string interp begin"
  show InterpEnd = "string interp end"
  show (StringLit n x) = "string" ++ Extra.replicate n '#' ++ " " ++ show x
  -- Identifiers
  show (HoleIdent x) = "hole identifier " ++ x
  show (Ident x) = "identifier " ++ x
  show (DotSepIdent ns n) = "namespaced identifier " ++ show ns ++ "." ++ show n
  show (DotIdent x) = "dot+identifier " ++ x
  show (Symbol x) = "symbol " ++ x
  -- Whitespace
  show Space = "whitespace"
  -- Comments
  show Comment = "comment"
  show (DocComment c) = "doc comment: \"" ++ c ++ "\""
  -- Special
  show (CGDirective x) = "CGDirective " ++ x
  show EndInput = "end of input"
  show (Keyword x) = x
  show (Pragma x) = "pragma " ++ x
  show (Unrecognised x) = "Unrecognised " ++ x

export
Pretty Token where
  -- Literals
  pretty (CharLit x) = pretty "character" <++> squotes (pretty x)
  pretty (DoubleLit x) = pretty "double" <++> pretty x
  pretty (IntegerLit x) = pretty "literal" <++> pretty x
  -- String
  pretty (StringBegin Single) = reflow "string begin"
  pretty (StringBegin Multi) = reflow "multiline string begin"
  pretty StringEnd = reflow "string end"
  pretty InterpBegin = reflow "string interp begin"
  pretty InterpEnd = reflow "string interp end"
  pretty (StringLit n x) = pretty ("string" ++ Extra.replicate n '#') <++> dquotes (pretty x)
  -- Identifiers
  pretty (HoleIdent x) = reflow "hole identifier" <++> pretty x
  pretty (Ident x) = pretty "identifier" <++> pretty x
  pretty (DotSepIdent ns n) = reflow "namespaced identifier" <++> pretty ns <+> dot <+> pretty n
  pretty (DotIdent x) = pretty "dot+identifier" <++> pretty x
  pretty (Symbol x) = pretty "symbol" <++> pretty x
  -- Whitespace
  pretty Space = pretty "space"
  -- Comments
  pretty Comment = pretty "comment"
  pretty (DocComment c) = reflow "doc comment:" <++> dquotes (pretty c)
  -- Special
  pretty (CGDirective x) = pretty "CGDirective" <++> pretty x
  pretty EndInput = reflow "end of input"
  pretty (Keyword x) = pretty x
  pretty (Pragma x) = pretty "pragma" <++> pretty x
  pretty (Unrecognised x) = pretty "Unrecognised" <++> pretty x

mutual
  ||| The mutually defined functions represent different states in a
  ||| small automaton.
  ||| `toEndComment` is the default state and it will munch through
  ||| the input until we detect a special character (a dash, an
  ||| opening brace, or a double quote) and then switch to the
  ||| appropriate state.
  toEndComment : (k : Nat) -> Recognise (k /= 0)
  toEndComment Z = empty
  toEndComment (S k)
               = some (pred (\c => c /= '-' && c /= '{' && c /= '"'))
                        <+> toEndComment (S k)
             <|> is '{' <+> singleBrace k
             <|> is '-' <+> singleDash k
             <|> stringLit <+> toEndComment (S k)

  ||| After reading a single brace, we may either finish reading an
  ||| opening delimiter or ignore it (e.g. it could be an implicit
  ||| binder).
  singleBrace : (k : Nat) -> Lexer
  singleBrace k
     =  is '-' <+> many (is '-')    -- opening delimiter
               <+> singleDash (S k) -- handles the {----} special case
    <|> toEndComment (S k)          -- not a valid comment

  ||| After reading a single dash, we may either find another one,
  ||| meaning we may have started reading a line comment, or find
  ||| a closing brace meaning we have found a closing delimiter.
  singleDash : (k : Nat) -> Lexer
  singleDash k
     =  is '-' <+> doubleDash k    -- comment or closing delimiter
    <|> is '}' <+> toEndComment k  -- closing delimiter
    <|> toEndComment (S k)         -- not a valid comment

  ||| After reading a double dash, we are potentially reading a line
  ||| comment unless the series of uninterrupted dashes is ended with
  ||| a closing brace in which case it is a closing delimiter.
  doubleDash : (k : Nat) -> Lexer
  doubleDash k = with Prelude.(::)
      many (is '-') <+> choice            -- absorb all dashes
        [ is '}' <+> toEndComment k                      -- closing delimiter
        , many (isNot '\n') <+> toEndComment (S k)       -- line comment
        ]

blockComment : Lexer
blockComment = is '{' <+> is '-' <+> toEndComment 1

docComment : Lexer
docComment = is '|' <+> is '|' <+> is '|' <+> many (isNot '\n')

holeIdent : Lexer
holeIdent = is '?' <+> identNormal

dotIdent : Lexer
dotIdent = is '.' <+> identNormal

pragma : Lexer
pragma = is '%' <+> identNormal

doubleLit : Lexer
doubleLit
    = digits <+> is '.' <+> digits <+> opt
           (is 'e' <+> opt (is '-' <|> is '+') <+> digits)

stringBegin : Lexer
stringBegin = many (is '#') <+> (is '"')

stringEnd : Nat -> String
stringEnd hashtag = "\"" ++ Extra.replicate hashtag '#'

multilineBegin : Lexer
multilineBegin = many (is '#') <+> (exact "\"\"\"") <+>
                    manyUntil newline space <+> newline

multilineEnd : Nat -> String
multilineEnd hashtag = "\"\"\"" ++ Extra.replicate hashtag '#'

-- Do this as an entire token, because the contents will be processed by
-- a specific back end
cgDirective : Lexer
cgDirective
    = exact "%cg" <+>
      ((some space <+>
           some (pred isAlphaNum) <+> many space <+>
           is '{' <+> many (isNot '}') <+>
           is '}')
         <|> many (isNot '\n'))

mkDirective : String -> Token
mkDirective str = CGDirective (trim (substr 3 (length str) str))

-- Reserved words
-- NB: if you add a new keyword, please add the corresponding documentation in
--     Idris.Doc.String
public export
keywords : List String
keywords = ["data", "module", "where", "let", "in", "do", "record",
            "auto", "default", "implicit", "mutual", "namespace",
            "parameters", "with", "proof", "impossible", "case", "of",
            "if", "then", "else", "forall", "rewrite",
            "using", "interface", "implementation", "open", "import",
            "public", "export", "private",
            "infixl", "infixr", "infix", "prefix",
            "total", "partial", "covering"]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

public export
symbols : List String
symbols = [",", ";", "_", "`"]

export
groupSymbols : List String
groupSymbols = [".(", -- for things such as Foo.Bar.(+)
    "@{", "[|", "(", "{", "[<", "[>", "[", "`(", "`{", "`["]

export
groupClose : String -> String
groupClose ".(" = ")"
groupClose "@{" = "}"
groupClose "[|" = "|]"
groupClose "(" = ")"
groupClose "[" = "]"
groupClose "[<" = "]"
groupClose "[>" = "]"
groupClose "{" = "}"
groupClose "`(" = ")"
groupClose "`{" = "}"
groupClose "`[" = "]"
groupClose _ = ""

export
isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

export
||| Test whether a user name begins with an operator symbol.
isOpUserName : UserName -> Bool
isOpUserName (Basic n) = fromMaybe False $ do
   c <- fst <$> strUncons n
   guard (isOpChar c)
   pure True
isOpUserName (Field _) = False
isOpUserName Underscore = False

export
||| Test whether a name begins with an operator symbol.
isOpName : Name -> Bool
isOpName = maybe False isOpUserName . userNameRoot

validSymbol : Lexer
validSymbol = some (pred isOpChar)

-- Valid symbols which have a special meaning so can't be operators
public export
reservedInfixSymbols : List String
reservedInfixSymbols
    = ["%", "\\", ":", "=", ":=", "$=", "|", "|||", "<-", "->", "=>", "?", "!",
       "&", "**", "..", "~", "@"]

-- Valid symbols which have a special meaning so can't be operators
public export
reservedSymbols : List String
reservedSymbols
    = symbols
    ++ groupSymbols ++ (groupClose <$> groupSymbols)
    ++ reservedInfixSymbols

fromBinLit : String -> Integer
fromBinLit str
    = if length str <= 2
         then 0
         else let num = assert_total (strTail (strTail str)) in
                fromBin . reverse . map castBin . unpack $ num
    where
      castBin : Char -> Integer
      castBin '1' = 1; castBin _ = 0 -- This can only be '1' and '0' once lexed
      fromBin : List Integer -> Integer
      fromBin [] = 0
      fromBin (0 :: xs) = 2 * fromBin xs
      fromBin (x :: xs) = x + (2 * fromBin xs)

fromHexLit : String -> Integer
fromHexLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             fromMaybe 0 (fromHex (reverse num))
             --        ^-- can't happen if the literal was lexed correctly

fromOctLit : String -> Integer
fromOctLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             fromMaybe 0 (fromOct (reverse num))
             --        ^-- can't happen if the literal lexed correctly

mutual
  stringTokens : Bool -> Nat -> Tokenizer Token
  stringTokens multi hashtag
      = let escapeChars = "\\" ++ Extra.replicate hashtag '#'
            interpStart = escapeChars ++ "{"
            escapeLexer = escape (exact escapeChars) any
            charLexer = non $ exact (if multi then multilineEnd hashtag else stringEnd hashtag)
          in
            match (someUntil (exact interpStart) (escapeLexer <|> charLexer)) (\x => StringLit hashtag x)
        <|> compose (exact interpStart)
                    (const InterpBegin)
                    (const ())
                    (\_ => rawTokens)
                    (const $ is '}')
                    (const InterpEnd)

  rawTokens : Tokenizer Token
  rawTokens =
          match comment (const Comment)
      <|> match blockComment (const Comment)
      <|> match docComment (DocComment . removeOptionalLeadingSpace . drop 3)
      <|> match cgDirective mkDirective
      <|> match holeIdent (\x => HoleIdent (assert_total (strTail x)))
      <|> compose (choice $ exact <$> groupSymbols)
                  Symbol
                  id
                  (\_ => rawTokens)
                  (exact . groupClose)
                  Symbol
      <|> match (choice $ exact <$> symbols) Symbol
      <|> match doubleLit (DoubleLit . cast)
      <|> match binUnderscoredLit (IntegerLit . fromBinLit . removeUnderscores)
      <|> match hexUnderscoredLit (IntegerLit . fromHexLit . removeUnderscores)
      <|> match octUnderscoredLit (IntegerLit . fromOctLit . removeUnderscores)
      <|> match digitsUnderscoredLit (IntegerLit . cast . removeUnderscores)
      <|> compose multilineBegin
                  (const $ StringBegin Multi)
                  countHashtag
                  (stringTokens True)
                  (exact . multilineEnd)
                  (const StringEnd)
      <|> compose stringBegin
                  (const $ StringBegin Single)
                  countHashtag
                  (stringTokens False)
                  (\hashtag => exact (stringEnd hashtag) <+> reject (is '"'))
                  (const StringEnd)
      <|> match charLit (CharLit . stripQuotes)
      <|> match dotIdent (\x => DotIdent (assert_total $ strTail x))
      <|> match namespacedIdent parseNamespace
      <|> match identNormal parseIdent
      <|> match pragma (\x => Pragma (assert_total $ strTail x))
      <|> match space (const Space)
      <|> match validSymbol Symbol
      <|> match symbol Unrecognised
    where
      parseIdent : String -> Token
      parseIdent x = if x `elem` keywords then Keyword x
                     else Ident x

      parseNamespace : String -> Token
      parseNamespace ns = case mkNamespacedIdent ns of
                               (Nothing, ident) => parseIdent ident
                               (Just ns, n)     => DotSepIdent ns n

      countHashtag : String -> Nat
      countHashtag = count (== '#') . unpack

      removeOptionalLeadingSpace : String -> String
      removeOptionalLeadingSpace str = case strM str of
                                            StrCons ' ' tail => tail
                                            _ => str

      removeUnderscores : String -> String
      removeUnderscores s = fastPack $ filter (/= '_') (fastUnpack s)

export
lexTo : Lexer ->
        String ->
        Either (StopReason, Int, Int, String)
               ( List (WithBounds ())     -- bounds of comments
               , List (WithBounds Token)) -- tokens
lexTo reject str
    = case lexTo reject rawTokens str of
           (toks, (EndInput, l, c, _)) =>
             -- Add the EndInput token so that we'll have a line and column
             -- number to read when storing spans in the file
             let end = [MkBounded EndInput False (MkBounds l c l c)] in
             Right $ map (++ end)
                   $ partitionEithers
                   $ map spotComment
                   $ filter isNotSpace toks
           (_, fail) => Left fail
    where

      isNotSpace : WithBounds Token -> Bool
      isNotSpace t = case t.val of
        Space => False
        _ => True

      spotComment : WithBounds Token ->
                    Either (WithBounds ()) (WithBounds Token)
      spotComment t = case t.val of
        Comment => Left (() <$ t)
        _ => Right t

export
lex : String ->
      Either (StopReason, Int, Int, String)
             ( List (WithBounds ())     -- bounds of comments
             , List (WithBounds Token)) -- tokens
lex = lexTo (pred $ const False)
