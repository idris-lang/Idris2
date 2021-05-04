module Another.One.Third

import A.Path.Of.Dires.First

%default total

export
map : (a -> b) -> Tree a -> Tree b
map f (Leaf a) = Leaf (f a)
map f (Node l r) = Node (map f l) (map f r)
