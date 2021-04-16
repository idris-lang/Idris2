module A.Path.Of.Dires.First

%default total

public export
data Tree : Type -> Type where
  Leaf : a -> Tree a
  Node : Tree a -> Tree a -> Tree a
