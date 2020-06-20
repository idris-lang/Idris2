module Parser.Lexer.Source

import public Parser.Lexer.Common

import Data.List
import Data.Strings
import Data.String.Extra

import Utils.Hex
import Utils.Octal
import Utils.String

%default total

public export
data Token
  -- Literals
  = CharLit String
  | DoubleLit Double
  | IntegerLit Integer
  | StringLit String
  -- Identifiers
  | HoleIdent String
  | Ident String
  | DotSepIdent (List String)  -- ident.ident
  | DotIdent String            -- .ident
  | Symbol String
  -- Comments
  | Comment String
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
  show (StringLit x) = "string " ++ show x
  -- Identifiers
  show (HoleIdent x) = "hole identifier " ++ x
  show (Ident x) = "identifier " ++ x
  show (DotSepIdent xs) = "namespaced identifier " ++ dotSep (reverse xs)
  show (DotIdent x) = "dot+identifier " ++ x
  show (Symbol x) = "symbol " ++ x
  -- Comments
  show (Comment _) = "comment"
  show (DocComment c) = "doc comment: \"" ++ c ++ "\""
  -- Special
  show (CGDirective x) = "CGDirective " ++ x
  show EndInput = "end of input"
  show (Keyword x) = x
  show (Pragma x) = "pragma " ++ x
  show (Unrecognised x) = "Unrecognised " ++ x

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
  doubleDash k = many (is '-') <+> choice      -- absorb all dashes
    [ is '}' <+> toEndComment k                -- closing delimiter
    , many (isNot '\n') <+> toEndComment (S k) -- line comment
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
keywords : List String
keywords = ["data", "module", "where", "let", "in", "do", "record",
            "auto", "default", "implicit", "mutual", "namespace",
            "parameters", "with", "impossible", "case", "of",
            "if", "then", "else", "forall", "rewrite",
            "using", "interface", "implementation", "open", "import",
            "public", "export", "private",
            "infixl", "infixr", "infix", "prefix",
            "total", "partial", "covering"]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

-- Special symbols - things which can't be a prefix of another symbol, and
-- don't match 'validSymbol'
export
symbols : List String
symbols
    = [".(", -- for things such as Foo.Bar.(+)
       "@{",
       "[|", "|]",
       "(", ")", "{", "}}", "}", "[", "]", ",", ";", "_",
       "`(", "`{{", "`[", "`"]

export
isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

validSymbol : Lexer
validSymbol = some (pred isOpChar)

-- Valid symbols which have a special meaning so can't be operators
export
reservedSymbols : List String
reservedSymbols
    = symbols ++
      ["%", "\\", ":", "=", "|", "|||", "<-", "->", "=>", "?", "!",
       "&", "**", "..", "~"]

fromHexLit : String -> Integer
fromHexLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             case fromHex (reverse num) of
                  Nothing => 0 -- can't happen if the literal lexed correctly
                  Just n => cast n

fromOctLit : String -> Integer
fromOctLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             case fromOct (reverse num) of
                  Nothing => 0 -- can't happen if the literal lexed correctly
                  Just n => cast n

rawTokens : TokenMap Token
rawTokens =
    [(comment, Comment),
     (blockComment, Comment),
     (docComment, DocComment . drop 3),
     (cgDirective, mkDirective),
     (holeIdent, \x => HoleIdent (assert_total (strTail x)))] ++
    map (\x => (exact x, Symbol)) symbols ++
    [(doubleLit, \x => DoubleLit (cast x)),
     (hexLit, \x => IntegerLit (fromHexLit x)),
     (octLit, \x => IntegerLit (fromOctLit x)),
     (digits, \x => IntegerLit (cast x)),
     (stringLit, \x => StringLit (stripQuotes x)),
     (charLit, \x => CharLit (stripQuotes x)),
     (dotIdent, \x => DotIdent (assert_total $ strTail x)),
     (namespacedIdent, parseNamespace),
     (identNormal, parseIdent),
     (pragma, \x => Pragma (assert_total $ strTail x)),
     (space, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]
  where
    parseIdent : String -> Token
    parseIdent x = if x `elem` keywords then Keyword x
                   else Ident x
    parseNamespace : String -> Token
    parseNamespace ns = case Data.List.reverse . split (== '.') $ ns of
                             [ident] => parseIdent ident
                             ns      => DotSepIdent ns

export
lexTo : (TokenData Token -> Bool) ->
        String -> Either (Int, Int, String) (List (TokenData Token))
lexTo pred str
    = case lexTo pred rawTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkToken l c l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex = lexTo (const False)
