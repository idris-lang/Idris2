module Main

import Data.Vect

factorialAux : Integer -> Integer -> Integer
factorialAux 0 a = a
factorialAux n a = factorialAux (n-1) (a*n)

factorial : Integer -> Integer
factorial n = factorialAux n 1

main : IO ()
main =
   do
      printLn $ factorial 100
      printLn $ factorial 10000
      printLn $ show $ the (Vect 3 String) ["red", "green", "blue"]
