module Main

import Data.So

total
lem1 : So x -> So (not x) -> Void
lem1 Oh Oh impossible

foo : Nat -> Int
foo z = 94
  where
    lem2 : So x -> So (not x) -> Void
    lem2 Oh Oh impossible
