expli_group : (a : String, b : Nat) -> String
expli_group a b = a ++ show b

impli_group : {a : String, b : Nat} -> String
impli_group {a} {b} = a ++ show b

expli_individual : (a : String) -> (b : Nat) -> String
expli_individual a b = a ++ show b

impli_individual : {a : String} -> {b : Nat} -> String
impli_individual {a} {b} = a ++ show b

main : IO ()
main = do
  printLn $ expli_group "a" 1
  printLn $ impli_group {a="a"} {b=1}
  printLn $ expli_individual "a" 1
  printLn $ impli_individual {a="a"} {b=1}
