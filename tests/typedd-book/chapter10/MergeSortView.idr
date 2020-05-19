import Data.List
import Data.List.Views

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne x = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
       = merge (mergeSort lefts | lrec)
               (mergeSort rights | rrec)
