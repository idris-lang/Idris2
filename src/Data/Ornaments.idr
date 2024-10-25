module Data.Ornaments

import Data.Desc

public export
data Inverse : {i, j : Type} -> (j -> i) -> i -> Type where
  Ok : (jval : j) -> Inverse m (m jval)

public export
data Orn : (j : Type) -> (j -> i) -> Desc i -> Type where
  Say : Inverse e i -> Orn j e (Say i)
  Sig : (s : Type) -> {d : s -> Desc i} -> ((sv : s) -> Orn j e (d sv)) -> Orn j e (Sig s d)
  Ask : Inverse e i -> Orn j e d -> Orn j e (Ask i d)
  Del : (s : Type) -> (s -> Orn j e d) -> Orn j e d

