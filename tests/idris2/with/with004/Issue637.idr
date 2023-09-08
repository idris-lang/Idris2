foo : Int -> Int
foo x with (x + 1)
  foo x | y = y + x

foo2 : Int
foo2 = foo 5
