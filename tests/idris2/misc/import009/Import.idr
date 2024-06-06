module Import

import Test

%hide Prelude.Ops.infixl.(|>)

(|>) : (s : HasComp x) => {0 a, b, c : x} -> a ~> b -> b ~> c -> a ~> c
a |> b = comp s a b

(~:>) : Type -> Type -> Type
a ~:> b = Pair a b
