import Data.List.Views

-- total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1, snocList input2)
  isSuffix _ _ | (Snoc x xs xsrec, Snoc y ys ysrec)
     = (x == y) && (isSuffix _ _ | (xsrec, ysrec))
  isSuffix _ _ | (Empty, s) = True
  isSuffix _ _ | (s, Empty) = False
