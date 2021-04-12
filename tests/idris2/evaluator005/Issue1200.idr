module Issue1200

%default total

main : IO ()
main = traverse_ printLn $ do
  f <- [(1/), log, sin, cos, tan, asin, acos, atan, sqrt, floor, ceiling]
  x <- [-2,-1,-0.5,0,0.5,1,2]
  pure (f x)
