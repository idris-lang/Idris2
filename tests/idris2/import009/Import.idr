module Import

import Test


(~:>) : Type -> Type -> Type
a ~:> b = Pair a b
