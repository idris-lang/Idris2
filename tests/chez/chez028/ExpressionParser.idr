module Main

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Nat
import Data.String.Parser
import Data.String.Parser.Expression

%default partial

table : OperatorTable Nat
table =
  [ [Infix (do token "^"; pure (power) ) AssocRight]
  , [ Infix (do token "*"; pure (*) ) AssocLeft ]
  , [ Infix (do token "+"; pure (+) ) AssocLeft ]
  ]

table' : OperatorTable Integer
table' =
  [ [ Infix (do token "*"; pure (*) ) AssocLeft
    , Infix (do token "/"; pure (div) ) AssocLeft
    ]
  , [ Infix (do token "+"; pure (+) ) AssocLeft
    , Infix (do token "-"; pure (-) ) AssocLeft
    ]
  ]

mutual
  term : Parser Nat
  term = (natural <|> expr) <* spaces
         <?> "simple expression"

  expr : Parser Nat
  expr = buildExpressionParser Nat table term

mutual
  term' : Parser Integer
  term' = (integer <|> expr') <* spaces
         <?> "simple expression"

  expr' : Parser Integer
  expr' = buildExpressionParser Integer table' term'

showRes : Show a => Either String (a, Int) -> IO ()
showRes res = case res of
                Left err => putStrLn err
                Right (xs, rem) => printLn xs

main : IO ()
main = do showRes (parse natural "5678")
          showRes (parse integer "-3")
          showRes (parse expr "1+4^3^2^1")
          showRes (parse expr' "4 + 2 * 3")
          showRes (parse expr' "13-3+1*2-10/2")
