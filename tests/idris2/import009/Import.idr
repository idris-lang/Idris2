module Import

import Test


testComp : List String -> Nat
testComp = map length |> fold (+) 0


(|:>) : Type -> Type -> Type
a |:> b = Pair a b
