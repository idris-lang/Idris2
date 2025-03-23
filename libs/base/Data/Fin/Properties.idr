||| Some properties of functions defined in `Data.Fin`
module Data.Fin.Properties

import public Data.Fin

import Syntax.PreorderReasoning

%default total

-------------------------------
--- `finToNat`'s properties ---
-------------------------------

||| A Fin's underlying natural number is smaller than the bound
export
elemSmallerThanBound : (n : Fin m) -> finToNat n `LT` m
elemSmallerThanBound FZ = LTESucc LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

||| Last's underlying natural number is the bound's predecessor
export
finToNatLastIsBound : {n : Nat} -> finToNat (Fin.last {n}) = n
finToNatLastIsBound {n=Z} = Refl
finToNatLastIsBound {n=S k} = cong S finToNatLastIsBound

||| Weaken does not modify the underlying natural number
export
finToNatWeakenNeutral : {n : Fin m} -> finToNat (weaken n) = finToNat n
finToNatWeakenNeutral = finToNatQuotient (weakenNeutral n)

||| WeakenN does not modify the underlying natural number
export
finToNatWeakenNNeutral : (0 m : Nat) -> (k : Fin n) ->
                         finToNat (weakenN m k) = finToNat k
finToNatWeakenNNeutral m k = finToNatQuotient (weakenNNeutral m k)

||| `Shift k` shifts the underlying natural number by `k`.
export
finToNatShift : (k : Nat) -> (a : Fin n) -> finToNat (shift k a) = k + finToNat a
finToNatShift Z     a = Refl
finToNatShift (S k) a = cong S (finToNatShift k a)

----------------------------------------------------
--- Complement (inversion) function's properties ---
----------------------------------------------------

export
complementSpec : {n : _} -> (i : Fin n) -> 1 + finToNat i + finToNat (complement i) = n
complementSpec {n = S k} FZ = cong S finToNatLastIsBound
complementSpec (FS k) = let H = complementSpec k in
  let h = finToNatWeakenNeutral {n = complement k} in
  cong S (rewrite h in H)

||| The inverse of a weakened element is the successor of its inverse
export
complementWeakenIsFS : {n : Nat} -> (m : Fin n) -> complement (weaken m) = FS (complement m)
complementWeakenIsFS FZ = Refl
complementWeakenIsFS (FS k) = cong weaken (complementWeakenIsFS k)

export
complementLastIsFZ : {n : Nat} -> complement (last {n}) = FZ
complementLastIsFZ {n = Z} = Refl
complementLastIsFZ {n = S n} = cong weaken (complementLastIsFZ {n})

||| `complement` is involutive (i.e. applied twice it is the identity)
export
complementInvolutive : {n : Nat} -> (m : Fin n) -> complement (complement m) = m
complementInvolutive FZ = complementLastIsFZ
complementInvolutive (FS k) = Calc $
   |~ complement (complement (FS k))
   ~~ complement (weaken (complement k)) ...( Refl )
   ~~ FS (complement (complement k))     ...( complementWeakenIsFS (complement k) )
   ~~ FS k                       ...( cong FS (complementInvolutive k) )

--------------------------------
--- Strengthening properties ---
--------------------------------

||| It's possible to strengthen a weakened element of Fin **m**.
export
strengthenWeakenIsRight : (n : Fin m) -> strengthen (weaken n) = Just n
strengthenWeakenIsRight FZ = Refl
strengthenWeakenIsRight (FS k) = rewrite strengthenWeakenIsRight k in Refl

||| It's not possible to strengthen the last element of Fin **n**.
export
strengthenLastIsLeft : {n : Nat} -> strengthen (Fin.last {n}) = Nothing
strengthenLastIsLeft {n=Z} = Refl
strengthenLastIsLeft {n=S k} = rewrite strengthenLastIsLeft {n=k} in Refl

||| It's possible to strengthen the inverse of a successor
export
strengthenNotLastIsRight : {n : Nat} -> (m : Fin n) -> strengthen (complement (FS m)) = Just (complement m)
strengthenNotLastIsRight m = strengthenWeakenIsRight (complement m)

||| Either tightens the bound on a Fin or proves that it's the last.
export
strengthen' : {n : Nat} -> (m : Fin (S n)) ->
              Either (m = Fin.last) (m' : Fin n ** finToNat m = finToNat m')
strengthen' {n = Z} FZ = Left Refl
strengthen' {n = S k} FZ = Right (FZ ** Refl)
strengthen' {n = S k} (FS m) = case strengthen' m of
    Left eq => Left $ cong FS eq
    Right (m' ** eq) => Right (FS m' ** cong S eq)

----------------------------
--- Weakening properties ---
----------------------------

export
weakenNZeroIdentity : (k : Fin n) ->  weakenN 0 k ~~~ k
weakenNZeroIdentity FZ = FZ
weakenNZeroIdentity (FS k) = FS (weakenNZeroIdentity k)

export
shiftFSLinear : (m : Nat) -> (f : Fin n) -> shift m (FS f) ~~~ FS (shift m f)
shiftFSLinear Z     f = reflexive
shiftFSLinear (S m) f = FS (shiftFSLinear m f)

export
shiftLastIsLast : (m : Nat) -> {n : Nat} ->
                  shift m (Fin.last {n}) ~~~ Fin.last {n=m+n}
shiftLastIsLast Z = reflexive
shiftLastIsLast (S m) = FS (shiftLastIsLast m)
