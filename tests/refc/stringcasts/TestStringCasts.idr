module Main

main : IO ()
main = do
  printLn (cast {to = Bits8}   "42")
  printLn (cast {to = Bits16}  "4242")
  printLn (cast {to = Bits32}  "424242")
  printLn (cast {to = Bits64}  "2000000000")
  printLn (cast {to = Int8}    "-42")
  printLn (cast {to = Int16}   "-4242")
  printLn (cast {to = Int32}   "-424242")
  printLn (cast {to = Int64}   "-2000000000")
  printLn (cast {to = Int}     "-42")
  printLn (cast {to = Integer} "-123456789012345678901234567890")
  printLn (cast {to = Nat}     "42")
  printLn (cast {to = Double}  "1.5")
  -- StrHead compiles to the head() macro, which uses the String -> Char cast
  printLn (prim__strHead "abc")
