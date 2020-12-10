module Data.Fin.Extra

import Data.Fin
import Data.Nat

%default total

-------------------------------
--- `finToNat`'s properties ---
-------------------------------

||| Proof that an element **n** of Fin **m** , when converted to Nat is smaller than the bound **m**.
export
elemSmallerThanBound : (n : Fin m) -> LT (finToNat n) m
elemSmallerThanBound FZ = LTESucc LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

||| Proof that application of finToNat the last element of Fin **S n** gives **n**.
export
finToNatLastIsBound : {n : Nat} -> finToNat (Fin.last {n}) = n
finToNatLastIsBound {n=Z} = Refl
finToNatLastIsBound {n=S k} = rewrite finToNatLastIsBound {n=k} in Refl

||| Proof that an element **n** of Fin **m** , when converted to Nat is smaller than the bound **m**.
export
finToNatWeakenNeutral : {m : Nat} -> {n : Fin m} -> finToNat (weaken n) = finToNat n
finToNatWeakenNeutral {n=FZ} = Refl
finToNatWeakenNeutral {m=S (S _)} {n=FS _} = cong S finToNatWeakenNeutral

export
finToNatWeakenNNeutral : (0 k : Nat) -> (a : Fin n) -> finToNat (weakenN k a) = finToNat a
finToNatWeakenNNeutral k FZ     = Refl
finToNatWeakenNNeutral k (FS x) = rewrite finToNatWeakenNNeutral k x in Refl

export
finToNatShift : (k : Nat) -> (a : Fin n) -> finToNat (shift k a) = k + finToNat a
finToNatShift Z     a = Refl
finToNatShift (S k) a = rewrite finToNatShift k a in Refl

-------------------------------------------------
--- Inversion function and related properties ---
-------------------------------------------------

||| Enumerate elements of Fin **n** backwards.
export
invFin : {n : Nat} -> Fin n -> Fin n
invFin FZ = last
invFin {n=S (S _)} (FS k) = weaken (invFin k)

||| Proof that an inverse of a weakened element of Fin **n** is a successive of an inverse of an original element.
export
invWeakenIsSucc : {n : Nat} -> (m : Fin n) -> invFin (weaken m) = FS (invFin m)
invWeakenIsSucc FZ = Refl
invWeakenIsSucc {n=S (S _)} (FS k) = rewrite invWeakenIsSucc k in Refl

||| Proof that double inversion of Fin **n** gives the original.
export
doubleInvFinSame : {n : Nat} -> (m : Fin n) -> invFin (invFin m) = m
doubleInvFinSame {n=S Z} FZ = Refl
doubleInvFinSame {n=S (S k)} FZ = rewrite doubleInvFinSame {n=S k} FZ in Refl
doubleInvFinSame {n=S (S _)} (FS x) = trans (invWeakenIsSucc $ invFin x) (cong FS $ doubleInvFinSame x)

||| Proof that an inverse of the last element of Fin (S **n**) in FZ.
export
invLastIsFZ : {n : Nat} -> invFin (Fin.last {n}) = FZ
invLastIsFZ {n=Z} = Refl
invLastIsFZ {n=S k} = rewrite invLastIsFZ {n=k} in Refl

--------------------------------
--- Strengthening properties ---
--------------------------------

||| Proof that it's possible to strengthen a weakened element of Fin **m**.
export
strengthenWeakenNeutral : {m : Nat} -> (n : Fin m) -> strengthen (weaken n) = Right n
strengthenWeakenNeutral {m=S _} FZ = Refl
strengthenWeakenNeutral {m=S (S _)} (FS k) = rewrite strengthenWeakenNeutral k in Refl

||| Proof that it's not possible to strengthen the last element of Fin **n**.
export
strengthenLastIsLeft : {n : Nat} -> strengthen (Fin.last {n}) = Left (Fin.last {n})
strengthenLastIsLeft {n=Z} = Refl
strengthenLastIsLeft {n=S k} = rewrite strengthenLastIsLeft {n=k} in Refl

-- ||| Proof that it's possible to strengthen an inverse of a succesive element of Fin **n**.
-- export
-- strengthenNotLastIsRight : (m : Fin (S n)) -> strengthen (invFin (FS m)) = Right (invFin m)
-- strengthenNotLastIsRight m = strengthenWeakenNeutral (invFin m)
--
||| Either tightens the bound on a Fin or proves that it's the last.
export
strengthen' : {n : Nat} -> (m : Fin (S n)) -> Either (m = Fin.last) (m' : Fin n ** finToNat m = finToNat m')
strengthen' {n = Z} FZ = Left Refl
strengthen' {n = S k} FZ = Right (FZ ** Refl)
strengthen' {n = S k} (FS m) = case strengthen' m of
    Left eq => Left $ cong FS eq
    Right (m' ** eq) => Right (FS m' ** cong S eq)

----------------------------
--- Weakening properties ---
----------------------------

export
weakenNZero_preserves : {a : Nat} -> (x : Fin a) -> weakenN 0 x = rewrite plusZeroRightNeutral a in x
weakenNZero_preserves {a=S i} FZ = rewrite plusZeroRightNeutral i in Refl
weakenNZero_preserves {a=S i} (FS x) = rewrite weakenNZero_preserves x in
                                       rewrite plusZeroRightNeutral i in
                                       Refl

-----------------------------------
--- Division-related properties ---
-----------------------------------

||| A view of Nat as a quotient of some number and a finite remainder.
public export
data FractionView : (n : Nat) -> (d : Nat) -> Type where
    Fraction : (n : Nat) -> (d : Nat) -> {auto ok: GT d Z} ->
                (q : Nat) -> (r : Fin d) ->
                q * d + finToNat r = n -> FractionView n d

||| Converts Nat to the fractional view with a non-zero divisor.
export
divMod : (n, d : Nat) -> {auto ok: GT d Z} -> FractionView n d
divMod Z (S d) = Fraction Z (S d) Z FZ Refl
divMod {ok=_} (S n) (S d) =
    let Fraction {ok=ok} n (S d) q r eq = divMod n (S d) in
    case strengthen' r of
        Left eq' => Fraction {ok=ok} (S n) (S d) (S q) FZ $
            rewrite sym eq in
                rewrite trans (cong finToNat eq') finToNatLastIsBound in
                    cong S $ trans
                        (plusZeroRightNeutral (d + q * S d))
                        (plusCommutative d (q * S d))
        Right (r' ** eq') => Fraction {ok=ok} (S n) (S d) q (FS r') $
            rewrite sym $ plusSuccRightSucc (q * S d) (finToNat r') in
                cong S $ trans (sym $ cong (plus (q * S d)) eq') eq

-------------------
--- Conversions ---
-------------------

||| Total function to convert a nat to a Fin, given a proof
||| that it is less than the bound.
public export
natToFinLTE : (n : Nat) -> (0 _ : LT n m) -> Fin m
natToFinLTE Z     (LTESucc _) = FZ
natToFinLTE (S k) (LTESucc l) = FS $ natToFinLTE k l

||| Converting from a Nat to a Fin and back is the identity.
public export
natToFinToNat :
  (n : Nat)
  -> (lte : LT n m)
  -> finToNat (natToFinLTE n lte) = n
natToFinToNat 0 (LTESucc lte) = Refl
natToFinToNat (S k) (LTESucc lte) = rewrite natToFinToNat k lte in Refl

----------------------------------------
--- Result-type changing arithmetics ---
----------------------------------------

public export
(+) : {a : Nat} -> Fin (S a) -> Fin (S b) -> Fin (S $ a + b)
(+) FZ y = rewrite plusCommutative a b in weakenN a y
(+) (FS x) y {a=S _} = FS $ x + y

public export
(*) : {a, b : Nat} -> Fin (S a) -> Fin (S b) -> Fin (S $ a * b)
(*) FZ _ = FZ
(*) (FS x) y {a=S i} = y + x * y

--- Properties ---

export
finToNat_plus_linearity : {a : Nat} -> (x : Fin $ S a) -> (y : Fin $ S b) -> finToNat (x + y) = finToNat x + finToNat y
finToNat_plus_linearity FZ     _         = rewrite plusCommutative a b in finToNatWeakenNNeutral _ _
finToNat_plus_linearity (FS x) y {a=S _} = rewrite finToNat_plus_linearity x y in Refl

export
finToNat_mult_linearity : {a, b : Nat} -> (x : Fin $ S a) -> (y : Fin $ S b) -> finToNat (x * y) = finToNat x * finToNat y
finToNat_mult_linearity FZ _ = Refl
finToNat_mult_linearity (FS x) y {a=S i} = rewrite finToNat_plus_linearity y (x * y) in
                                           rewrite finToNat_mult_linearity x y in
                                           Refl

export
plusSuccRightSucc : {a, b : Nat} -> (left : Fin $ S a) -> (right : Fin $ S b) -> FS (left + right) = rewrite plusSuccRightSucc a b in left + FS right
plusSuccRightSucc FZ     right         = rewrite plusCommutative a b in Refl
plusSuccRightSucc (FS x) right {a=S i} = rewrite plusSuccRightSucc x right in
                                         rewrite plusSuccRightSucc i b in
                                         Refl

export
shiftAsPlus : {a, b : Nat} -> (x : Fin $ S a) -> shift b x = rewrite sym $ plusSuccRightSucc b a in last {n=b} + x
shiftAsPlus {b=Z}   x = rewrite weakenNZero_preserves x in Refl
shiftAsPlus {b=S k} x = rewrite shiftAsPlus {b=k} x in
                        rewrite plusSuccRightSucc k a in
                        Refl

export
weakenNAsPlusFZ : {a, b : Nat} -> (x : Fin $ S b) -> weakenN a x = x + the (Fin $ S a) FZ
weakenNAsPlusFZ FZ = rewrite plusCommutative a b in Refl
weakenNAsPlusFZ (FS x) {b=S j} = rewrite weakenNAsPlusFZ {a} x in Refl

export
weakenNOfPlus : {a, b : Nat} -> (n : Nat) -> (x : Fin $ S a) -> (y : Fin $ S b) ->
                weakenN n (x + y) = rewrite sym $ plusAssociative a b n in
                                    rewrite plusCommutative b n in
                                    rewrite plusAssociative a n b in
                                    weakenN n x + y
weakenNOfPlus n FZ FZ = rewrite sym $ plusAssociative b a n in
                        rewrite plusCommutative a n in
                        rewrite plusAssociative b n a in
                        Refl
weakenNOfPlus n FZ (FS y) {b=S j} = rewrite sym $ weakenNOfPlus {a} n FZ y in
                                    rewrite plusCommutative j a in
                                    rewrite sym $ plusAssociative a j n in
                                    rewrite plusAssociative j a n in
                                    rewrite plusCommutative j a in
                                    rewrite plusAssociative a j n in
                                    Refl
weakenNOfPlus n (FS x) y {a=S i} = rewrite weakenNOfPlus n x y in
                                   rewrite sym $ plusAssociative i n b in
                                   rewrite plusCommutative n b in
                                   rewrite plusAssociative i b n in
                                   Refl

export
plusCommutative : {a, b : Nat} -> (left : Fin $ S a) -> (right : Fin $ S b) -> left + right = rewrite plusCommutative a b in right + left
plusCommutative FZ     right = rewrite plusCommutative a b in weakenNAsPlusFZ {a} right
plusCommutative (FS x) right {a=S i} = rewrite sym $ plusSuccRightSucc right x in
                                       rewrite plusCommutative x right in
                                       rewrite plusCommutative b i in
                                       Refl

export
plusAssociative : {a, b, c : Nat} -> (left : Fin $ S a) -> (centre : Fin $ S b) -> (right : Fin $ S c) ->
                  left + (centre + right) = rewrite plusAssociative a b c in (left + centre) + right
plusAssociative FZ centre right = rewrite weakenNOfPlus {a=b} {b=c} a centre right in
                                  rewrite plusCommutative b a in
                                  Refl
plusAssociative (FS x) centre right {a=S i} = rewrite plusAssociative x centre right in
                                              rewrite plusAssociative i b c in
                                              Refl

-------------------------------------------------
--- Splitting operations and their properties ---
-------------------------------------------------

export
splitSumFin : {a : Nat} -> Fin (a + b) -> Either (Fin a) (Fin b)
splitSumFin {a=Z}   x      = Right x
splitSumFin {a=S k} FZ     = Left FZ
splitSumFin {a=S k} (FS x) = mapFst FS $ splitSumFin x

export
splitProdFin : {a, b : Nat} -> Fin (a * b) -> (Fin a, Fin b)
splitProdFin {a=S _} x = case splitSumFin x of
  Left  y => (FZ, y)
  Right y => mapFst FS $ splitProdFin y

--- Properties ---

export
splitSumFin_correctness : {a, b : Nat} -> (x : Fin $ a + b) ->
                          case splitSumFin {a} {b} x of
                            Left  l => x = weakenN b l
                            Right r => x = shift a r
splitSumFin_correctness {a=Z}   x  = Refl
splitSumFin_correctness {a=S k} FZ = Refl
splitSumFin_correctness {a=S k} (FS x) with (splitSumFin_correctness x)
  splitSumFin_correctness {a=S k} (FS x) | subcorr with (splitSumFin x)
    splitSumFin_correctness {a=S k} (FS x) | subcorr | Left  y = rewrite subcorr in Refl
    splitSumFin_correctness {a=S k} (FS x) | subcorr | Right y = rewrite subcorr in Refl

export
splitProdFin_correctness : {a, b : Nat} -> (x : Fin $ S a * S b) ->
                           let (o, i) = splitProdFin {a=S a} {b=S b} x in
                           x = i + o * last {n=S b}
splitProdFin_correctness x with (splitSumFin_correctness {a=S b} x)
  splitProdFin_correctness x | sumcorr with (splitSumFin {a=S b} x)
    splitProdFin_correctness x | sumcorr | Left  y = rewrite sumcorr in weakenNAsPlusFZ {a=mult a (S b)} y
    splitProdFin_correctness x | sumcorr | Right y with (a)
      splitProdFin_correctness x | sumcorr | Right y | S i with (splitProdFin_correctness y)
        splitProdFin_correctness x | sumcorr | Right y | S i | subcorr with (splitProdFin {a=S i} {b=S b} y)
          splitProdFin_correctness x | sumcorr | Right y | S i | subcorr | (oo, ii) =
            rewrite sumcorr in
            rewrite subcorr in
            rewrite sym $ plusSuccRightSucc ii $ last {n=b} + (oo * FS (last {n=b})) in
            rewrite shiftAsPlus {b} $ ii + (oo * FS (last {n=b})) in
            rewrite plusAssociative (last {n=b}) ii $ (oo * FS (last {n=b})) in
            rewrite plusCommutative (last {n=b}) ii in
            rewrite plusAssociative ii (last {n=b}) $ (oo * FS (last {n=b})) in
            rewrite plusSuccRightSucc b $ b + i * S b in
            Refl
