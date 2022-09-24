expli : (a : String, b : Nat) -> String
expli a b = a ++ show b

impli : {a : String, b : Nat} -> String
impli {a} {b} = a ++ show b

main : IO ()
main = do
  printLn $ expli "a" 1
  printLn $ impli {a="a"} {b=1}
