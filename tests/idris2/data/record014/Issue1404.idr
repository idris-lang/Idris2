
total
record Bar where
  constructor MkBar
  good : (Int -> Int) -> Bar
  bad  : (Bar -> Int) -> Bar
