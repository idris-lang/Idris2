module Data.Vect.Sort

import Data.Vect
import Data.Nat.Views

mutual
  sortBySplit : (n : Nat) -> (a -> a -> Ordering) -> Vect n a -> Vect n a
  sortBySplit Z cmp [] = []
  sortBySplit (S Z) cmp [x] = [x]
  sortBySplit n cmp xs with (half n)
    sortBySplit (k + k) cmp xs     | HalfEven k = sortByMerge k k cmp xs
    sortBySplit (S (k + k)) cmp xs | HalfOdd k = sortByMerge (S k) k cmp xs

  sortByMerge : (n : Nat) -> (m : Nat) -> (a -> a -> Ordering) -> Vect (n + m) a -> Vect (n + m) a
  sortByMerge n m cmp xs =
    let (left, right) = splitAt n xs in
      mergeBy cmp
        (sortBySplit n cmp (assert_smaller xs left))
        (sortBySplit m cmp (assert_smaller xs right))

||| Merge sort implementation for Vect n a
export total
sortBy : {n : Nat} -> (cmp : a -> a -> Ordering) -> (xs : Vect n a) -> Vect n a
sortBy {n} cmp xs = sortBySplit n cmp xs

export total
sort : Ord a => {n : Nat} -> Vect n a -> Vect n a
sort = sortBy compare
