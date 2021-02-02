module Test

export
pythag : Int -> List (Int, Int, Int)
pythag max
    = [ (x,y,z) | z <- [1..max],
                  y <- [1..z],
                  x <- [1..y],

                  x * x + y * y == z * z ]

namespace Inside
  -- Needs to be recursive (or at least refer to a name in this module)
  -- to check that definitions are updated on import...as
  export
  fact : Nat -> Nat
  fact Z = 1
  fact (S k) = (S k) * fact k

public export
interface Needle a where
  nardle : a -> a
  noo : a -> a
