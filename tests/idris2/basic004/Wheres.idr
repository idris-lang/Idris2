module Wheres

import Stuff

reverse : List a -> List a
reverse xs = rev' Nil xs
  where
    rev' : List a -> List a -> List a
    rev' acc Nil = acc
    rev' acc (x :: xs) = rev' (x :: acc) xs

foo : Int -> Int
foo x = case isLT of
            Yes => prim__mul_Int x 2
            No => prim__mul_Int x 4
  where
    data MyLT = Yes | No

    isLT : MyLT
    isLT = ifThenElse (intToBool (prim__lt_Int x 20)) Yes No
