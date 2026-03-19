module TestDebugInfo

-- A minimal program to verify #line directives appear in generated C
-- and that --directive debug produces a valid debug build.

greet : String -> String
greet name = "Hello, " ++ name ++ "!"

main : IO ()
main = putStrLn (greet "debug")
