%default total

data Tree a = Node a (Tree a) (Tree a)

failing "Nope is not total, not strictly positive"

  data Nope : Type where
    MkNope : Tree (Not Nope) -> Nope

covering
data Yep : Type where
  MkYep : Tree (Not Yep) -> Yep
