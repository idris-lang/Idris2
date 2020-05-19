import Data.Stream

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith lbls [] = []
labelWith (lbl :: lbls) (val :: vals) = (lbl, val) :: labelWith lbls vals

label : List a -> List (Integer, a)
label vals = labelWith (iterate (+1) 0) vals
