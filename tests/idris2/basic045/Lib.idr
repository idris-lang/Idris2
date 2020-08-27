module Lib

import Data.List

%default total

export
accMapAux : (a -> b) -> List a -> List b -> List b
accMapAux f [] acc = reverse acc
accMapAux f (x :: xs) acc = accMapAux f xs (f x :: acc)

public export
accMap : (a -> b) -> List a -> List b
accMap f xs = accMapAux f xs []
