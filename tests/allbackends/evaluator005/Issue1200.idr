module Issue1200

%default total

show' : Double -> String
show' d = if d == (1/0) then "Infinity"
          else if d == (-1/0) then "-Infinity"
          else if d /= d then "NaN"
          else show $ cast {to=Int} (d*100000)

main : IO ()
main = traverse_ (putStrLn . show') $ do
  f <- [(1/), log, sin, cos, tan, asin, acos, atan, sqrt, floor, ceiling]
  x <- [-2,-1,-0.5,0,0.5,1,2]
  pure (f x)
