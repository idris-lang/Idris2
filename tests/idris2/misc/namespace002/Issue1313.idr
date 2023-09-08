namespace X

  export
  f : Int -> Int

namespace Y

  g : Int -> Int -> Int
  g x y = x + f g

namespace X

  f 5 = 6
  f x = x - 1
