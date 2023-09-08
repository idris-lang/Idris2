main : IO ()
main = do
  putStrLn $ show (the Bits64 0xffffffffffffffff)
  putStrLn $ show (the Bits64 0x8000000000000000)
