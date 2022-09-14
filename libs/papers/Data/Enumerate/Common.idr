module Data.Enumerate.Common

import Data.List

%default total

export
prodWith : (a -> b -> c) -> List a -> List b -> List c
prodWith f [] bs = []
prodWith f as [] = []
prodWith f (a :: as) (b :: bs) = f a b :: interleave (map (f a) bs) (prodWith f as (b :: bs))
