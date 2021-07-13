module Main

import Data.List

%default partial

large : (a: Type) -> a
-- integer larger than 64 bits
large Integer = 3518437212345678901234567890123
-- int close to 2ˆ63
-- we expect some operations will overflow
large Int = 9223372036854775800

small : (a: Type) -> a
small Integer = 437
small Int = 377

numOps : (Num a) => List ( a -> a -> a )
numOps = [ (+), (*) ]

negOps : (Neg a) => List (a -> a -> a)
negOps = [ (-) ]

integralOps : (Integral a) => List (a -> a -> a)
integralOps = [ div, mod ]

binOps : (Num a, Neg a, Integral a) => List (a -> a -> a)
binOps = numOps ++ negOps ++ integralOps

main : IO ()
main = do
  putStrLn $ show (results Integer)
  putStrLn $ show (results Int)
  where
  results : (a:Type) -> (Num a, Neg a, Integral a) => List a
  results a = map (\ op => large a  `op` small a) binOps
