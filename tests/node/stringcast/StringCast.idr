main : IO ()
main = do
  printLn $ cast {to = Integer} "end"
  printLn $ cast {to = Nat} "end"
  printLn $ cast {to = Double} "end"
  printLn $ cast {to = Bits8} "end"
  printLn $ cast {to = Bits16} "end"
  printLn $ cast {to = Bits32} "end"
  printLn $ cast {to = Bits64} "end"
  printLn $ cast {to = Int8} "end"
  printLn $ cast {to = Int16} "end"
  printLn $ cast {to = Int32} "end"
  printLn $ cast {to = Int64} "end"
  printLn $ cast {to = Int} "end"
