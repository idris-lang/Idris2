import Data.SnocList

sing : a -> List a
sing = pure

main : IO ()
main = do
  printLn $ foldr (::) Nil [< 1,2,3]
  printLn $ foldMap sing [< 1,2,3]
