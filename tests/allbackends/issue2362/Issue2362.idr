module Issue2362

import Data.Vect

%default total

items : Vect ? String
items = [ "0.0", "0", "0.", ".0", "+0", "-0", "string", "" ]

zeroes_double : Vect ? Double
zeroes_double = cast <$> items

zeroes_show : Vect ? String
zeroes_show = show <$> zeroes_double

main : IO ()
main = do
  printLn $ all (== head zeroes_double) zeroes_double
  printLn $ all (== head zeroes_show) zeroes_show
