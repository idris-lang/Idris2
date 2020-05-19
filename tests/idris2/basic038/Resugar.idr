module Resugar

niceList : List (Nat, Nat)
niceList = [ (i, j) | i <- [0..4], j <- [5..9] ]
