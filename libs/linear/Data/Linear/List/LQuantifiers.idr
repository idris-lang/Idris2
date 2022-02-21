module Data.Linear.List.LQuantifiers

import Data.Linear.Notation

%default total

public export
data LAll : (p : a -> Type) -> List a -> Type where
  Nil  : LAll p []
  (::) : p x -@ LAll p xs -@ LAll p (x :: xs)
