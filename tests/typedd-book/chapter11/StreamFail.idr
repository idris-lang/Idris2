countFrom : Integer -> List Integer
countFrom n = n :: countFrom (n + 1)

labelWith : List Integer -> List a -> List (Integer, a)
labelWith lbls [] = []
labelWith (lbl :: lbls) (val :: vals) = (lbl, val) :: labelWith lbls vals
