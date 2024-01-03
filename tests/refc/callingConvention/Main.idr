module Main

%default total

last : List a -> a -> a
last [] x = x
last (y :: ys) _ = last ys y

main : IO ()
main = flip for_ (printLn . (`last` 0))
     $ [] :: map (\ x => [1..x]) [1..5]
