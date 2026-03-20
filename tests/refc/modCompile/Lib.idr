module Lib

export
greet : String -> String
greet name = "Hello, " ++ name ++ "!"

export
add : Int -> Int -> Int
add x y = x + y
