module Data.Nat.Div

import Data.Nat

%default total

||| Divides n by 2 (rounding down), returning `p = n / 2` and
||| `q = n - (n / 2)`, along with a proof that `p + q = n`.
export
div2 : (n : Nat) -> (p ** (q ** (p + q = n)))
div2 Z = (Z ** (Z ** Refl))
div2 (S Z) = (Z ** ((S Z) ** Refl))
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
