import Data.List
import Data.List1
import Text.Lexer
import Text.Parser

%default total

data Expr = App Expr Expr | Abs String Expr | Var String | Let String Expr Expr

Show Expr where
  showPrec d (App e1 e2) = showParens (d == App) (showPrec (User 0) e1 ++ " " ++ showPrec App e2)
  showPrec d (Abs v e) = showParens (d > Open) ("\\" ++ v ++ "." ++ show e)
  showPrec d (Var v) = v
  showPrec d (Let v e1 e2) = showParens (d > Open) ("let " ++ v ++ " = " ++ show e1 ++ " in " ++ show e2)

data LambdaTokenKind
  = LTLambda
  | LTIdentifier
  | LTDot
  | LTOParen
  | LTCParen
  | LTIgnore
  | LTLet
  | LTEqual
  | LTIn

Eq LambdaTokenKind where
  (==) LTLambda LTLambda = True
  (==) LTDot LTDot = True
  (==) LTIdentifier LTIdentifier = True
  (==) LTOParen LTOParen = True
  (==) LTCParen LTCParen = True
  (==) LTLet LTLet = True
  (==) LTEqual LTEqual = True
  (==) LTIn LTIn = True
  (==) _ _ = False

Show LambdaTokenKind where
  show LTLambda = "LTLambda"
  show LTDot = "LTDot"
  show LTIdentifier = "LTIdentifier"
  show LTOParen = "LTOParen"
  show LTCParen = "LTCParen"
  show LTIgnore = "LTIgnore"
  show LTLet = "LTLet"
  show LTEqual = "LTEqual"
  show LTIn = "LTIn"

LambdaToken : Type
LambdaToken = Token LambdaTokenKind

Show LambdaToken where
  show (Tok kind text) = "Tok kind: " ++ show kind ++ " text: " ++ text

TokenKind LambdaTokenKind where
  TokType LTIdentifier = String
  TokType _ = ()

  tokValue LTLambda _ = ()
  tokValue LTIdentifier s = s
  tokValue LTDot _ = ()
  tokValue LTOParen _ = ()
  tokValue LTCParen _ = ()
  tokValue LTIgnore _ = ()
  tokValue LTLet _ = ()
  tokValue LTEqual _ = ()
  tokValue LTIn _ = ()

ignored : WithBounds LambdaToken -> Bool
ignored (MkBounded (Tok LTIgnore _) _ _) = True
ignored _ = False

identifier : Lexer
identifier = alpha <+> many alphaNum

keywords : List (String, LambdaTokenKind)
keywords = [
  ("let", LTLet),
  ("in", LTIn)
]

lambdaTokenMap : TokenMap LambdaToken
lambdaTokenMap = toTokenMap [(spaces, LTIgnore)] ++
  [(identifier, \s =>
      case lookup s keywords of
        (Just kind) => Tok kind s
        Nothing => Tok LTIdentifier s
    )
  ] ++ toTokenMap [
    (exact "\\", LTLambda),
    (exact ".", LTDot),
    (exact "(", LTOParen),
    (exact ")", LTCParen),
    (exact "=", LTEqual)
  ]

lexLambda : String -> Maybe (List (WithBounds LambdaToken))
lexLambda str =
  case lex lambdaTokenMap str of
    (tokens, _, _, "") => Just tokens
    _ => Nothing

mutual
  expr : Grammar state LambdaToken True Expr
  expr = do
    t <- term
    app t <|> pure t

  term : Grammar state LambdaToken True Expr
  term = abs
    <|> var
    <|> paren
    <|> letE

  app : Expr -> Grammar state LambdaToken True Expr
  app e1 = do
    e2 <- term
    app1 $ App e1 e2

  app1 : Expr -> Grammar state LambdaToken False Expr
  app1 e = app e <|> pure e

  abs : Grammar state LambdaToken True Expr
  abs = do
    match LTLambda
    commit
    argument <- match LTIdentifier
    match LTDot
    e <- expr
    pure $ Abs argument e

  var : Grammar state LambdaToken True Expr
  var = map Var $ match LTIdentifier

  paren : Grammar state LambdaToken True Expr
  paren = do
    match LTOParen
    e <- expr
    match LTCParen
    pure e

  letE : Grammar state LambdaToken True Expr
  letE = do
    match LTLet
    commit
    argument <- match LTIdentifier
    match LTEqual
    e1 <- expr
    match LTIn
    e2 <- expr
    pure $ Let argument e1 e2

parseLambda : List (WithBounds LambdaToken) -> Either String Expr
parseLambda toks =
  case parse expr $ filter (not . ignored) toks of
    Right (l, []) => Right l
    Right e => Left "contains tokens that were not consumed"
    Left e => Left (show e)

parse : String -> Either String Expr
parse x =
  case lexLambda x of
    Just toks => parseLambda toks
    Nothing => Left "Failed to lex."
