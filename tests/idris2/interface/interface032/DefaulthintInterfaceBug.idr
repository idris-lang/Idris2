namespace Data

  interface X where
    x : Nat

  data Y : Type where
    MkY : Nat -> Y

  Y => X where
    x @{MkY y} = y

  %defaulthint
  DefY : Y
  DefY = MkY 6

  f : X => IO ()
  f = printLn x

  main : IO ()
  main = f

namespace Interface

  interface X' where
    x' : Nat

  interface Y' where
    constructor MkY
    y' : Nat

  Y' => X' where
    x' = y'

  %defaulthint
  DefY' : Y'
  DefY' = MkY 6

  f' : X' => IO ()
  f' = printLn x'

  main : IO ()
  main = f'
