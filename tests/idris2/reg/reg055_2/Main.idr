module Main

import Declaration

Declaration.f x y = do
  putStrLn x
  putStrLn y

main : IO ()
main = f "first" "second"
