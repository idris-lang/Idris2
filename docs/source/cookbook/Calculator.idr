import Data.List1
import Text.Lexer
import Text.Parser
import Text.Parser.Expression

%default total

data CalculatorTokenKind
  = CTNum
  | CTPlus
  | CTMinus
  | CTMultiply
  | CTDivide
  | CTOParen
  | CTCParen
  | CTIgnore

Eq CalculatorTokenKind where
  (==) CTNum CTNum = True
  (==) CTPlus CTPlus = True
  (==) CTMinus CTMinus = True
  (==) CTMultiply CTMultiply = True
  (==) CTDivide CTDivide = True
  (==) CTOParen CTOParen = True
  (==) CTCParen CTCParen = True
  (==) _ _ = False

Show CalculatorTokenKind where
  show CTNum = "CTNum"
  show CTPlus = "CTPlus"
  show CTMinus = "CTMinus"
  show CTMultiply = "CTMultiply"
  show CTDivide = "CTDivide"
  show CTOParen = "CTOParen"
  show CTCParen = "CTCParen"
  show CTIgnore = "CTIgnore"

CalculatorToken : Type
CalculatorToken = Token CalculatorTokenKind

Show CalculatorToken where
    show (Tok kind text) = "Tok kind: " ++ show kind ++ " text: " ++ text

TokenKind CalculatorTokenKind where
  TokType CTNum = Double
  TokType _ = ()

  tokValue CTNum s = cast s
  tokValue CTPlus _ = ()
  tokValue CTMinus _ = ()
  tokValue CTMultiply _ = ()
  tokValue CTDivide _ = ()
  tokValue CTOParen _ = ()
  tokValue CTCParen _ = ()
  tokValue CTIgnore _ = ()

ignored : WithBounds CalculatorToken -> Bool
ignored (MkBounded (Tok CTIgnore _) _ _) = True
ignored _ = False

number : Lexer
number = digits

calculatorTokenMap : TokenMap CalculatorToken
calculatorTokenMap = toTokenMap [
  (spaces, CTIgnore),
  (digits, CTNum),
  (exact "+", CTPlus),
  (exact "-", CTMinus),
  (exact "*", CTMultiply),
  (exact "/", CTDivide)
]

lexCalculator : String -> Maybe (List (WithBounds CalculatorToken))
lexCalculator str =
  case lex calculatorTokenMap str of
    (tokens, _, _, "") => Just tokens
    _ => Nothing

mutual
  term : Grammar state CalculatorToken True Double
  term = do
    num <- match CTNum
    pure num

  expr : Grammar state CalculatorToken True Double
  expr = buildExpressionParser [
    [ Infix ((*) <$ match CTMultiply) AssocLeft
    , Infix ((/) <$ match CTDivide) AssocLeft
    ],
    [ Infix ((+) <$ match CTPlus) AssocLeft
    , Infix ((-) <$ match CTMinus) AssocLeft
    ]
  ] term

parseCalculator : List (WithBounds CalculatorToken) -> Either String Double
parseCalculator toks =
  case parse expr $ filter (not . ignored) toks of
    Right (l, []) => Right l
    Right e => Left "contains tokens that were not consumed"
    Left e => Left (show e)

parse1 : String -> Either String Double
parse1 x =
  case lexCalculator x of
    Just toks => parseCalculator toks
    Nothing => Left "Failed to lex."
