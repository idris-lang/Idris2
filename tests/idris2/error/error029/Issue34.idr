data T : Type -> Type where
  Leaf : T a
  Node : Ord a => a -> T a -> T a -> T a

zipWith : (a -> a -> a) -> T a -> T a -> T a
zipWith f Leaf _ = Leaf
zipWith f _ Leaf = Leaf
zipWith f (Node x lx rx) (Node y ly ry)
  = Node (f x y) (zipWith f lx ly) (zipWith f rx ry)
