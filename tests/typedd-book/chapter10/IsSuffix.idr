import Data.List.Views

-- total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (MkPair (snocList input1) (snocList input2))
  isSuffix [] input2 | (Empty, s) = True
  isSuffix input1 [] | (s, Empty) = False
  isSuffix (xs ++ [x]) (ys ++ [y]) | (MkPair (Snoc x xs xsrec) (Snoc y ys ysrec))
     = if x == y
          then isSuffix xs ys | (MkPair xsrec ysrec)
          else False
