module Core.Name.ScopedList.Name

import Core.Name
import Core.Name.ScopedList

export
namesEq : (xs, ys : ScopedList Name) -> Maybe (xs = ys)
namesEq [<] [<] = Just Refl
namesEq (x :%: xs) (y :%: ys)
    = do p <- nameEq x y
         ps <- namesEq xs ys
         rewrite p
         rewrite ps
         Just Refl
namesEq _ _ = Nothing
