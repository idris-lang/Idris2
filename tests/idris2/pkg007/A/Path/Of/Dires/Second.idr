module A.Path.Of.Dires.Second

import public A.Path.Of.Dires.First

%default total

export
example : Tree Nat
example = Node (Node (Leaf 0) (Leaf 1)) (Leaf 2)
