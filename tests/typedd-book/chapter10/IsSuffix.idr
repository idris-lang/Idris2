import Data.List.Views

total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc x xs xsrec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc x xs xsrec) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc x xs xsrec) | (Snoc y ys ysrec)
      = if x == y then isSuffix xs ys | xsrec else False
