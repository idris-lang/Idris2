namespace A
  export
  foo3 : Int -> Int
  foo3 x with (x + 1)
  foo3 x | y = y + x

foo4 : Int
foo4 = A.foo3 5
