infixl 7 <><

public export
(<><) : SnocList a -> List a -> SnocList a
sx <>< [] = sx
sx <>< (x :: xs) = (sx :< x) <>< xs
