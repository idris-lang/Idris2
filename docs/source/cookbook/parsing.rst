Parsing
=======

Idris 2 comes with a Lexing and a Parsing library built into the ``contrib`` package.

For this cookbook, we will write a very simple parser for a lambda calculus parser
that will accept the following language:

.. code-block:: text

    let name = world in (\x.hello x) name

Once we write a lambda calculus parser, we will also see how we can take advantage of a
powerful built in expression parser in Idris 2 to write a small calculator that should be
smart enough to parse the following expression:

.. code-block:: text

    1 + 2 - 3 * 4 / 5

Lexer
-----

The main lexer module is under ``Text.Lexer``. This module contains ``toTokenMap`` which is a function
that converts a ``List (Lexer, k) -> TokenMap (Token k)`` where ``k`` is a token kind. This function
could be used for simple lexer to token mappings. The module also includes high level lexers for
specifying quantity and common programming primitives like ``alphas``, ``intLit``,
``lineComment`` and ``blockComment``.

The ``Text.Lexer`` module also reexports ``Text.Lexer.Core``, ``Text.Quantity`` and ``Text.Token``.

``Text.Lexer.Core`` provides the building blocks of the lexer, including a type called
``Recognise`` which is the underlying data type for the lexer. The other important function that this
module provides is a ``lex`` which takes in a lexer and returns the tokens.

``Text.Quantity`` provides a data type ``Quantity`` which can be used with certain lexers to specify
how many times something is expected to appear.

``Text.Token`` provides a data type ``Token`` that represents a parsed token, its kind and the text.
This module also provides an important interface called ``TokenKind`` which tells the lexer how to map
token kinds to Idris 2 types and how to convert each kind from a string to a value.

Parser
------

The main parser module is under ``Text.Parser``. This module contains different grammar parsers, the main
one being ``match`` which takes a ``TokenKind`` and returns the value as defined in the ``TokenKind``
interface. There are other grammar parsers as well, but for our example, we will only be using ``match``.

The ``Text.Parser`` module reexports ``Text.Parser.Core``, ``Text.Quantity`` and ``Text.Token``.

``Text.Parser.Core`` provides the building blocks of the parser, including a type called ``Grammar``
which is the underlying data type for the parser. The other important function that this module provides
is ``parse`` which takes in a ``Grammar`` and returns the parsed expression.

We covered ``Text.Quantity`` and ``Text.Token`` in the Lexer section so we're not going to
repeat what they do here.

Lambda Calculus Lexer & Parser
------------------------------

.. code-block:: idris
    :caption: LambdaCalculus.idr
    :linenos:

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

Testing out our parser gives us back the following output:

.. code-block:: text

    $ idris2 -p contrib LambdaCalculus.idr
    Main> :exec printLn $ parse "let name = world in (\\x.hello x) name"
    Right (let name = world in (\x.hello x) name)

Expression Parser
-----------------

Idris 2 also comes with a very convenient expression parser that is
aware of precedence and associativity in ``Text.Parser.Expression``.

The main function called ``buildExpressionParser`` takes in an ``OperatorTable`` and a
``Grammar`` that represents the terms, and returns a parsed expression. The magic comes from
the ``OperatorTable`` since this table defines all the operators, the grammars for those operators,
the precedence, and the associativity.

An ``OperatorTable`` is a list of lists containing the ``Op`` type. The ``Op`` type allows you to specify
``Prefix``, ``Postfix``, and ``Infix`` operators along with their grammars. ``Infix`` also contains the
associativity called ``Assoc`` which can specify left associativity or ``AssocLeft``, right
associativity assoc or ``AssocRight`` and as being non-associative or ``AssocNone``.

An example of an operator table we'll be using for the calculator is:

.. code-block:: idris

    [
      [ Infix (match CTMultiply >> pure (*)) AssocLeft
      , Infix (match CTDivide >> pure (/)) AssocLeft
      ],
      [ Infix (match CTPlus >> pure (+)) AssocLeft
      , Infix (match CTMinus >> pure (-)) AssocLeft
      ]
    ]

This table defines 4 operators for mulitiplication, division, addition and subtraction.
Mulitiplication and division show up in the first table because they have higher precedence than
addition and subtraction, which show up in the second table. We're also defining them as infix operators,
with a specific grammar and all being left associative via ``AssocLeft``.

Building a Calculator
---------------------

.. code-block:: idris
    :caption: Calculator.idr
    :linenos:

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

Testing out our calculator gives us back the following output:

.. code-block:: text

    $ idris2 -p contrib Calculator.idr
    Main> :exec printLn $ parse1 "1 + 2 - 3 * 4 / 5"
    Right 0.6000000000000001
