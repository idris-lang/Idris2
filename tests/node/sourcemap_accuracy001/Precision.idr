module Main

-- Line 4: function definition
add : Int -> Int -> Int
add x y = x + y

-- Line 8: another function
multiply : Int -> Int -> Int
multiply x y = x * y

-- Line 12: main with multiple lines
main : IO ()
main = do
  let a = add 1 2        -- Line 14
  let b = multiply 3 4   -- Line 15
  printLn a              -- Line 16
  printLn b              -- Line 17
