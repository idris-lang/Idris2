-- Test integer comparison operations
-- Regression test for WASM32 comparison bug where idris2_extractInt
-- incorrectly handled unboxed boolean values on 32-bit platforms.
module Main

testIntEq : Int -> Int -> String
testIntEq a b = if a == b then "EQ" else "NE"

testIntLt : Int -> Int -> String
testIntLt a b = if a < b then "LT" else "GE"

testIntGt : Int -> Int -> String
testIntGt a b = if a > b then "GT" else "LE"

testIntLte : Int -> Int -> String
testIntLte a b = if a <= b then "LTE" else "GT"

testIntGte : Int -> Int -> String
testIntGte a b = if a >= b then "GTE" else "LT"

main : IO ()
main = do
  -- Equality tests
  putStrLn $ "5 == 5: " ++ testIntEq 5 5
  putStrLn $ "5 == 10: " ++ testIntEq 5 10
  putStrLn $ "0 == 0: " ++ testIntEq 0 0
  putStrLn $ "-1 == -1: " ++ testIntEq (-1) (-1)
  putStrLn $ "-1 == 1: " ++ testIntEq (-1) 1

  -- Less than tests
  putStrLn $ "5 < 10: " ++ testIntLt 5 10
  putStrLn $ "10 < 5: " ++ testIntLt 10 5
  putStrLn $ "5 < 5: " ++ testIntLt 5 5

  -- Greater than tests
  putStrLn $ "10 > 5: " ++ testIntGt 10 5
  putStrLn $ "5 > 10: " ++ testIntGt 5 10
  putStrLn $ "5 > 5: " ++ testIntGt 5 5

  -- Less than or equal tests
  putStrLn $ "5 <= 10: " ++ testIntLte 5 10
  putStrLn $ "5 <= 5: " ++ testIntLte 5 5
  putStrLn $ "10 <= 5: " ++ testIntLte 10 5

  -- Greater than or equal tests
  putStrLn $ "10 >= 5: " ++ testIntGte 10 5
  putStrLn $ "5 >= 5: " ++ testIntGte 5 5
  putStrLn $ "5 >= 10: " ++ testIntGte 5 10
