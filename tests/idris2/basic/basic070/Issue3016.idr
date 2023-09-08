import Data.String

test str = len
  where
    xs = words str
    len = length xs

parameters (n : Nat) (strs : List String)
  len = List.length strs
