{-

Test that some library functions don't cause "Maximum call stack size exceeded"
errors.

So far, only Prelude.List.++ is tested.

-}

module Main

import Data.List
import Data.SnocList

values : List Nat
values = replicate 50000 1

seulav : SnocList Nat
seulav = Lin <>< values

main : IO ()
main = do
  printLn $ length $ values ++ [1]
  printLn $ length $ map Just values
  printLn $ length $ mapMaybe Just values
  printLn $ length $ filter (const True) values
  printLn $ length $ seulav ++ [<1]
  printLn $ length $ map Just seulav
  printLn $ length $ mapMaybe Just seulav
  printLn $ length $ filter (const True) seulav
