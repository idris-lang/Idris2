data BST : a -> Type where
  Leaf : BST a
  Node : (root : a) -> (lt : BST a) -> (rt : BST a) -> BST a

-- Checking that we can look under the @ to get rt and lt
total
insert : Ord a => a -> BST a -> BST a
insert p Leaf = Node p Leaf Leaf
insert p tree@(Node root lt rt) =
  case p `compare` root of
    GT => Node root lt (insert p rt)
    EQ => tree
    LT => Node root (insert p lt) rt
