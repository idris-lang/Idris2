module Data.Vect.Sort

import Data.Vect
import Data.Nat.Div

||| Merge sort implementation for Vect n a
export total
sortBy : {n : Nat} -> (cmp : a -> a -> Ordering) -> (xs : Vect n a) -> Vect n a
sortBy cmp [] = []
sortBy cmp [x] = [x]
sortBy cmp xs =
    let (p ** (q ** equalityProof)) = div2 n in
        let (left, right) = splitAt p (pqRewrite equalityProof xs) in
            rewrite sym equalityProof in
                mergeBy cmp
                    (sortBy cmp (assert_smaller xs left))
                    (sortBy cmp (assert_smaller xs right))
        where
            pqRewrite : (p + q = n) -> Vect n a -> Vect (p + q) a
            pqRewrite equalityProof xs = rewrite equalityProof in xs

sort : Ord a => {n : Nat} -> Vect n a -> Vect n a
sort = sortBy compare
