module Main

add : Int -> Int -> Int
add x y = x + y

main : IO ()
main = do
  putStrLn "Source map test"
  printLn (add 1 2)
