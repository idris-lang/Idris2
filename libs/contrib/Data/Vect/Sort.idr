module Data.Vect.Sort

import Data.Vect
import Data.Nat

-- Merge sort implementation for Vect n a
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

            -- Divides n by 2 (rounding down), returning `p = n / 2` and
            -- `q = n - (n / 2)`, along with a proof that `p + q = n`.
            div2 : (n : Nat) -> (p ** (q ** (p + q = n)))
            div2 Z = (Z ** (Z ** Refl))
            div2 (S Z )= (Z ** ((S Z) ** Refl))
            div2 (S (S n)) = 
                let (p' ** (q' ** equalityProof)) = div2 n in
                    let almostProof = proofHelper equalityProof in
                        let updatedProof = cong (S) almostProof in
                            ((S p') ** ((S q') ** updatedProof))
                    where
                        proofHelper : (p + q = n) -> (p + (S q) = (S n))
                        proofHelper {p} {q} baseProof =
                            rewrite sym (plusSuccRightSucc p q) in
                                cong (S) baseProof

sort : Ord a => {n : Nat} -> Vect n a -> Vect n a
sort = sortBy compare
