-- Port of https://hackage.haskell.org/package/parsec-3.1.13.0/docs/Text-Parsec-Expr.html
-- Original License	BSD-style: https://hackage.haskell.org/package/parsec-3.1.13.0/src/LICENSE

module Data.String.Parser.Expression

import Data.String.Parser

public export
data Assoc = AssocNone
           | AssocLeft
           | AssocRight

public export
data Operator a = Infix (Parser (a -> a -> a)) Assoc
                | Prefix (Parser (a -> a))
                | Postfix (Parser (a -> a))

public export
OperatorTable : Type -> Type
OperatorTable a = List (List (Operator a))

public export
BinaryOperator : Type -> Type
BinaryOperator a = List (Parser (a -> a -> a))

public export
UnaryOperator : Type -> Type
UnaryOperator a = List (Parser (a -> a))

public export
data Ops a = BinOp (BinaryOperator a) | UnOp (UnaryOperator a)

public export
ReturnType : Type -> Type
ReturnType a = (BinaryOperator a, BinaryOperator a, BinaryOperator a, UnaryOperator a, UnaryOperator a)

toParserBin : BinaryOperator a -> Parser (a -> a -> a)
toParserBin [] = fail "couldn't create binary parser"
toParserBin (x :: xs) = x <|> toParserBin xs

toParserUn : UnaryOperator a -> Parser (a -> a)
toParserUn [] = fail "couldn't create unary parser"
toParserUn (x :: xs) = x <|> toParserUn xs

ambiguous : (assoc : String) -> (op : Parser (a -> a -> a)) -> Parser a
ambiguous assoc op = do ignore op
                        fail ("ambiguous use of a " ++ assoc ++ " associative operator")

mutual
  mkRassocP : (amLeft : Parser a) -> (amNon : Parser a) -> (rassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkRassocP amLeft amNon rassocOp termP x =
   (do f <- rassocOp
       y <- do z <- termP ; mkRassocP1 amLeft amNon rassocOp termP z
       pure (f x y))
   <|> (amLeft)
   <|> (amNon)

  mkRassocP1 : (amLeft : Parser a) -> (amNon : Parser a) -> (rassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkRassocP1 amLeft amNon rassocOp termP x = (mkRassocP amLeft amNon rassocOp termP x) <|> pure x

mutual
  mkLassocP : (amRight : Parser a) -> (amNon : Parser a) -> (lassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkLassocP amRight amNon lassocOp termP x =
    (do f <- lassocOp
        y <- termP
        mkLassocP1 amRight amNon lassocOp termP (f x y))
    <|> amRight
    <|> amNon

  mkLassocP1 : (amRight : Parser a) -> (amNon : Parser a) -> (lassocOp : Parser (a -> a -> a)) -> (termP : Parser a) -> (x : a) -> Parser a
  mkLassocP1 amRight amNon lassocOp termP x = mkLassocP amRight amNon lassocOp termP x <|> pure x

mkNassocP : (amRight, amLeft, amNon : Parser a) ->
            (nassocOp : Parser (a -> a -> a)) ->
            (termP : Parser a) -> (x : a) -> Parser a
mkNassocP amRight amLeft amNon nassocOp termP x =
  do f <- nassocOp
     y <- termP
     ignore (amRight <|> amLeft <|> amNon)
     pure (f x y)

public export
buildExpressionParser : (a : Type) -> OperatorTable a -> Parser a -> Parser a
buildExpressionParser a operators simpleExpr =
  foldl (makeParser a) simpleExpr operators
  where
    splitOp : (a : Type) -> Operator a -> ReturnType a -> ReturnType a
    splitOp x (Infix op AssocNone) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, op :: nassoc, prefixx, postfix)
    splitOp x (Infix op AssocLeft) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, op :: lassoc, nassoc, prefixx, postfix)
    splitOp x (Infix op AssocRight) (rassoc, lassoc, nassoc, prefixx, postfix) = (op :: rassoc, lassoc, nassoc, prefixx, postfix)
    splitOp x (Prefix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, op :: prefixx, postfix)
    splitOp x (Postfix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, prefixx, op :: postfix)

    makeParser : (a : Type) -> Parser a -> List (Operator a) -> Parser a
    makeParser a term ops =
      let (rassoc,lassoc,nassoc
               ,prefixx,postfix) = foldr (splitOp a) ([],[],[],[],[]) ops
          rassocOp = toParserBin rassoc
          lassocOp = toParserBin lassoc
          nassocOp = toParserBin nassoc
          prefixxOp = toParserUn prefixx
          postfixOp = toParserUn postfix

          amRight = ambiguous "right" rassocOp
          amLeft = ambiguous "left" lassocOp
          amNon = ambiguous "non" nassocOp

          prefixxP = prefixxOp <|> pure (\x => x)

          postfixP = postfixOp <|> pure (\x => x)

          termP = do pre <- prefixxP
                     x <- term
                     post <- postfixP
                     pure (post (pre x))

          rassocP = mkRassocP amLeft amNon rassocOp termP
          lassocP = mkLassocP amRight amNon lassocOp termP
          nassocP = mkNassocP amRight amLeft amNon nassocOp termP
      in
          do x <- termP
             rassocP x <|> lassocP x <|> nassocP x <|> pure x <?> "operator"
