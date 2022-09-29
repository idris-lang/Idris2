import Data.Nat

main : IO ()
main = do
  printLn (the Bits8 0xff + 100)
  printLn (the Nat 12345)
  printLn (the Nat (-12345))
  printLn (271 `minus` 12)
