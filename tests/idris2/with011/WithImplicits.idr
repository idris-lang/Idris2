import Data.Vect
import Data.Vect.Views.Extra

mergeSort : Ord a => {n : _} -> Vect n a -> Vect n a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (xs ++ ys) | (SplitRecPair {xs} {ys} xs_rec ys_rec) =
    merge (mergeSort xs | xs_rec) (mergeSort ys | ys_rec)
