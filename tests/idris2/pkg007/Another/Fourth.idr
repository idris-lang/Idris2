module Another.Fourth

import A.Path.Of.Dires.Second
import Another.One.Third

%default total

example2 : Tree Nat
example2 = map S example
