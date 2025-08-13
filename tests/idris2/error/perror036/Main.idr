main : IO ()
main = do
  let foo = 10
  printLn "foo = \{show foo"
  let bar = 10 * (1 + foo)
  printLn "bar = \{show bar}"

