module CastStringDouble

%default total

main : IO ()
main = traverse_ printLn $ do
  f <- [(1/), log, sin, cos, tan, asin, acos, atan, sqrt, floor, ceiling]
  v <- [ "", "-1", "-1.0", "-1.", "0", "0.", ".0", ".1", "1", "1.0", "+0", "+1", "+.1", "+1.0", "string", "+nan.0", "+inf.0" ]
  pure (floor $ f (cast v))
