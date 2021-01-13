module Main

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Nat
import Data.String.Parser
import Data.String.Parser.Expression

%default partial

table : OperatorTable Nat
table =
  [ [ Infix (token "^" $> power ) AssocRight]
  , [ Infix (token "*" $> (*)   ) AssocLeft ]
  , [ Infix (token "+" $> (+)   ) AssocLeft ]
  ]

table' : OperatorTable Integer
table' =
  [ [ Infix (token "*" $> (*) ) AssocLeft
    , Infix (token "/" $> div ) AssocLeft
    ]
  , [ Infix (token "+" $> (+) ) AssocLeft
    , Infix (token "-" $> (-) ) AssocLeft
    ]
  ]

mutual
  term : Parser Nat
  term = lexeme (natural <|> expr)
         <?> "simple expression"

  expr : Parser Nat
  expr = buildExpressionParser Nat table term

mutual
  term' : Parser Integer
  term' = lexeme (integer <|> expr')
          <?> "simple expression"

  expr' : Parser Integer
  expr' = buildExpressionParser Integer table' term'

run : Show a => Parser a -> String -> IO ()
run p s = case parse (p <* eos) s of
                Left err => putStrLn err
                Right (xs, _) => printLn xs

main : IO ()
main = do run natural "5678"
          run integer "-3"
          run expr "1+4^3^2^1"
          run expr' "4 + 2 * 3"
          run expr' "13-3+1*2-10/2"
