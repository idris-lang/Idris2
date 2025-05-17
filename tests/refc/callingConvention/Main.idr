module Main

%default total

dupargs : Integer -> Integer
dupargs x = x + x

last : List a -> a -> a
last [] x = x
last (y :: ys) _ = last ys y

main : IO ()
main = do
  flip for_ (printLn . (`last` 0))
     $ [] :: map (\ x => [1..x]) [1..5]
  printLn $ dupargs 9999

