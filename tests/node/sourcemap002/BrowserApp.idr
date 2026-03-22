module Main

-- Simple browser-style app for testing --cg javascript source maps
greet : String -> String
greet name = "Hello, " ++ name ++ "!"

main : IO ()
main = putStrLn (greet "World")
