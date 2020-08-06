module Main

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Maybe
import Data.Fin
import Data.Nat
import Data.String.Parser
import Data.String.Parser.Expression

%default partial

addDigit : Nat -> Nat -> Nat
addDigit num d = 10*num + d

fromDigits : List Nat -> Nat
fromDigits xs = foldl addDigit 0 xs

digit : Parser Nat
digit = do x <- satisfy isDigit
           case fromChar x of
                Nothing => P $ \s => do pure $ Fail s.pos "not a digit"
                Just y => P $ \s => Id (OK y s)
  where fromChar : Char -> Maybe Nat
        fromChar '0' = Just 0
        fromChar '1' = Just 1
        fromChar '2' = Just 2
        fromChar '3' = Just 3
        fromChar '4' = Just 4
        fromChar '5' = Just 5
        fromChar '6' = Just 6
        fromChar '7' = Just 7
        fromChar '8' = Just 8
        fromChar '9' = Just 9
        fromChar _ = Nothing

natural : Parser Nat
natural = do x <- some digit
             pure (fromDigits x)

skip : Parser a -> Parser ()
skip = map (const ())

space : Parser Char
space = satisfy isSpace

spaces : Parser ()
spaces = skip (many space) <?> "white space"

lexeme : Parser a -> Parser a
lexeme p = p <* spaces

token : String -> Parser ()
token s = lexeme (skip (string s)) <?> "token " ++ show s

table : OperatorTable Nat
table =
  [ [Infix (do token "^"; pure (power) ) AssocRight]
  , [Infix (do token "*"; pure (*) ) AssocLeft]
  , [Infix (do token "+"; pure (+) ) AssocLeft]]

mutual
  term : Parser Nat
  term = (natural <|> expr) <* spaces
         <?> "simple expression"

  expr : Parser Nat
  expr = buildExpressionParser Nat table term

showRes : Show a => Either String (a, Int) -> IO ()
showRes res = case res of
                Left err => putStrLn err
                Right (xs, rem) => printLn xs

main : IO ()
main = do showRes (parse natural "5678")
          showRes (parse expr "1 + 2 * 3")
          showRes (parse expr "1+4^3^2^1")
