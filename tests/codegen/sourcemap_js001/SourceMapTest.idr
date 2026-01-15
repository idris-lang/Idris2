module Main

greet : String -> String
greet name = "Hello, " ++ name ++ "!"

main : IO ()
main = putStrLn (greet "World")
