           module UninhIndent

           data MyElem : a -> List a -> Type where
             MyHere : MyElem x (x :: xs)
             MyThere : (later : MyElem x xs) -> MyElem x (y :: xs)

           Uninhabited (MyElem a []) where
             uninhabited c = ?uninhabited_rhs
