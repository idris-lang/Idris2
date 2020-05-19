
labelFrom : Integer -> List a -> List (Integer, a)
labelFrom lbl [] = []
labelFrom lbl (val :: vals) = (lbl, val) :: labelFrom (lbl + 1) vals

label : List a -> List (Integer, a)
label = labelFrom 0
