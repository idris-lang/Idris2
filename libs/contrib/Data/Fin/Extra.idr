module Data.Fin.Extra

import Data.Fin
import Data.Nat

import Syntax.WithProof

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

export
shift_FS_linear : (a : Nat) -> {0 b : Nat} -> (0 x : Fin b) -> shift a (FS x) = rewrite sym $ plusSuccRightSucc a b in FS (shift a x)
shift_FS_linear Z     x = Refl
shift_FS_linear (S k) x = rewrite shift_FS_linear k x in
                          rewrite plusSuccRightSucc k b in
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
plus_preserves_last : (a, b : Nat) -> Fin.last {n=a} + Fin.last {n=b} = Fin.last
plus_preserves_last Z     b = rewrite weakenNZero_preserves $ Fin.last {n=b} in Refl
plus_preserves_last (S k) b = rewrite plus_preserves_last k b in Refl

export
mult_preserves_last : (a, b : Nat) -> Fin.last {n=a} * Fin.last {n=b} = Fin.last
mult_preserves_last Z     b = Refl
mult_preserves_last (S k) b = rewrite mult_preserves_last k b in plus_preserves_last _ _

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

public export
indexSum : {a : Nat} -> Either (Fin a) (Fin b) -> Fin (a + b)
indexSum $ Left  l = weakenN b l
indexSum $ Right r = shift a r

public export
splitSum : {a : Nat} -> Fin (a + b) -> Either (Fin a) (Fin b)
splitSum {a=Z}   x      = Right x
splitSum {a=S k} FZ     = Left FZ
splitSum {a=S k} (FS x) = mapFst FS $ splitSum x

public export
indexProd : {b : Nat} -> Fin a -> Fin b -> Fin (a * b)
indexProd FZ     = weakenN $ mult (pred a) b
indexProd (FS x) = shift b . indexProd x

public export
splitProd : {a, b : Nat} -> Fin (a * b) -> (Fin a, Fin b)
splitProd {a=S _} x = case splitSum x of
  Left  y => (FZ, y)
  Right y => mapFst FS $ splitProd y

--- Properties ---

export
indexSum_preserves_last : (a, b : Nat) -> indexSum {a} (Right $ Fin.last {n=b}) = rewrite sym $ plusSuccRightSucc a b in Fin.last {n=a+b}
indexSum_preserves_last Z     b = Refl
indexSum_preserves_last (S k) b = rewrite indexSum_preserves_last k b in
                                  rewrite plusSuccRightSucc k b in
                                  Refl

export
indexProd_preserves_last : (a, b : Nat) -> indexProd (Fin.last {n=a}) (Fin.last {n=b}) = Fin.last
indexProd_preserves_last Z b = rewrite weakenNZero_preserves $ Fin.last {n=b} in
                               rewrite plusZeroRightNeutral b in
                               Refl
indexProd_preserves_last (S k) b = rewrite indexProd_preserves_last k b in
                                   rewrite shiftAsPlus {b} $ last {n=pred $ S k * S b} in
                                   rewrite plus_preserves_last b $ pred $ S k * S b in
                                   rewrite sym $ plusSuccRightSucc b $ pred $ S k * S b in
                                   Refl

splitSum_of_weakenN : (l : Fin a) -> Left l = splitSum {b} (weakenN b l)
splitSum_of_weakenN FZ = Refl
splitSum_of_weakenN (FS x) = cong (mapFst FS) $ splitSum_of_weakenN {b} x

splitSum_of_shift : {a : Nat} -> (r : Fin b) -> Right r = splitSum {a} (shift a r)
splitSum_of_shift {a=Z}   r = Refl
splitSum_of_shift {a=S k} r = cong (mapFst FS) $ splitSum_of_shift {a=k} r

export
split_of_index_sum_inverse : {a : Nat} -> (e : Either (Fin a) (Fin b)) -> e = splitSum (indexSum e)
split_of_index_sum_inverse (Left l) = splitSum_of_weakenN l
split_of_index_sum_inverse (Right r) = splitSum_of_shift r

export
index_of_split_sum_inverse : {a, b : Nat} -> (f : Fin (a + b)) -> f = indexSum (splitSum {a} {b} f)
index_of_split_sum_inverse {a=Z}   f  = Refl
index_of_split_sum_inverse {a=S k} FZ = Refl
index_of_split_sum_inverse {a=S k} (FS x) with (index_of_split_sum_inverse {a=k} {b} x)
  index_of_split_sum_inverse {a=S _} (FS x) | sub with (splitSum x)
    index_of_split_sum_inverse {a=S _} (FS _) | sub | Left  _ = rewrite sub in Refl
    index_of_split_sum_inverse {a=S _} (FS _) | sub | Right _ = rewrite sub in Refl

export
split_of_index_prod_inverse : {a : Nat} -> (x : Fin a) -> (y : Fin b) -> (x, y) = splitProd (indexProd x y)
split_of_index_prod_inverse {a=S k} FZ     y = rewrite sym $ splitSum_of_weakenN {b=mult k b} y in Refl
split_of_index_prod_inverse {a=S k} (FS x) y = rewrite sym $ splitSum_of_shift {a=b} $ indexProd x y in
                                               cong (mapFst FS) $ split_of_index_prod_inverse x y

export
index_of_split_prod_inverse : {a, b : Nat} -> (f : Fin (a * b)) -> f = uncurry (indexProd {a} {b}) (splitProd {a} {b} f)
index_of_split_prod_inverse {a=S k} f with (@@ splitSum f)
  index_of_split_prod_inverse f | (Left l ** prf) = rewrite prf in
                                                    rewrite sym $ cong indexSum prf in
                                                    index_of_split_sum_inverse f
  index_of_split_prod_inverse f | (Right r ** prf) = rewrite prf in
                                                     rewrite index_of_split_sum_inverse {a=b} {b=mult k b} f in
                                                     rewrite cong indexSum prf in
                                                     rewrite indexProd_of_mapFst_FS {a=k} {b} $ splitProd r in
                                                     cong (shift b) $ index_of_split_prod_inverse r where
    indexProd_of_mapFst_FS : {b : Nat} -> (x : (Fin a, Fin b)) -> uncurry (indexProd {b}) (mapFst FS x) = shift b (uncurry (indexProd {b}) x)
    indexProd_of_mapFst_FS (x, y) = Refl
