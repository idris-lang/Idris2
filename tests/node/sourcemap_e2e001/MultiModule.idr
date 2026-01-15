module Main

-- A more complex sample with multiple constructs to test source map accuracy
-- Each function has a comment indicating its expected source line

-- Line 7: Simple function
greet : String -> String
greet name = "Hello, " ++ name

-- Line 11: Pattern matching function
describe : Nat -> String
describe Z = "zero"
describe (S Z) = "one"
describe (S (S n)) = "many: " ++ show (S (S n))

-- Line 17: Case expression
classify : Int -> String
classify n = case compare n 0 of
  LT => "negative"
  EQ => "zero"
  GT => "positive"

-- Line 24: Do-notation with multiple bindings
processNumbers : IO ()
processNumbers = do
  let x = 10
  let y = 20
  let z = x + y
  putStrLn $ "Sum: " ++ show z

-- Line 32: Higher-order function
applyTwice : (a -> a) -> a -> a
applyTwice f x = f (f x)

-- Line 36: Where clause
calculateArea : Double -> Double
calculateArea radius = pi * radius * radius
  where
    pi : Double
    pi = 3.14159

-- Line 43: Main entry point
main : IO ()
main = do
  putStrLn (greet "World")
  putStrLn (describe 5)
  putStrLn (classify (-3))
  processNumbers
  putStrLn $ "Doubled: " ++ show (applyTwice (*2) 3)
  putStrLn $ "Area: " ++ show (calculateArea 2.0)
