range : Integer -> Integer -> List Integer
range bottom top
    = if bottom > top then []
         else bottom :: range (bottom + 1) top

pythag : Integer -> List (Integer, Integer, Integer)
pythag top
   = [(x, y, z) | z <- range 1 top, y <- range 1 z, x <- range 1 y,
                  x * x + y * y == z * z]
