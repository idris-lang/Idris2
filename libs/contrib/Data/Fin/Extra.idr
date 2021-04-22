module Data.Fin.Extra

import Data.Fin
import Data.Nat

import Syntax.WithProof
import Syntax.PreorderReasoning

%default total

-------------------------------
--- `finToNat`'s properties ---
-------------------------------

||| A Fin's underlying natural number is smaller than the bound
export
elemSmallerThanBound : (n : Fin m) -> LT (finToNat n) m
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

-------------------------------------------------
--- Inversion function and related properties ---
-------------------------------------------------

||| Compute the Fin such that `k + invFin k = n - 1`
export
invFin : {n : Nat} -> Fin n -> Fin n
invFin FZ = last
invFin (FS k) = weaken (invFin k)

||| The inverse of a weakened element is the successor of its inverse
export
invFinWeakenIsFS : {n : Nat} -> (m : Fin n) -> invFin (weaken m) = FS (invFin m)
invFinWeakenIsFS FZ = Refl
invFinWeakenIsFS (FS k) = cong weaken (invFinWeakenIsFS k)

export
invFinLastIsFZ : {n : Nat} -> invFin (last {n}) = FZ
invFinLastIsFZ {n = Z} = Refl
invFinLastIsFZ {n = S n} = cong weaken (invFinLastIsFZ {n})

||| `invFin` is involutive (i.e. applied twice it is the identity)
export
invFinInvolutive : {n : Nat} -> (m : Fin n) -> invFin (invFin m) = m
invFinInvolutive FZ = invFinLastIsFZ
invFinInvolutive (FS k) = Calc $
   |~ invFin (invFin (FS k))
   ~~ invFin (weaken (invFin k)) ...( Refl )
   ~~ FS (invFin (invFin k))     ...( invFinWeakenIsFS (invFin k) )
   ~~ FS k                       ...( cong FS (invFinInvolutive k) )

--------------------------------
--- Strengthening properties ---
--------------------------------

||| It's possible to strengthen a weakened element of Fin **m**.
export
strengthenWeakenIsRight : (n : Fin m) -> strengthen (weaken n) = Right n
strengthenWeakenIsRight FZ = Refl
strengthenWeakenIsRight (FS k) = rewrite strengthenWeakenIsRight k in Refl

||| It's not possible to strengthen the last element of Fin **n**.
export
strengthenLastIsLeft : {n : Nat} -> strengthen (Fin.last {n}) = Left (Fin.last {n})
strengthenLastIsLeft {n=Z} = Refl
strengthenLastIsLeft {n=S k} = rewrite strengthenLastIsLeft {n=k} in Refl

||| It's possible to strengthen the inverse of a succesor
export
strengthenNotLastIsRight : {n : Nat} -> (m : Fin n) -> strengthen (invFin (FS m)) = Right (invFin m)
strengthenNotLastIsRight m = strengthenWeakenIsRight (invFin m)

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
natToFinToNat (S k) (LTESucc lte) = cong S (natToFinToNat k lte)

----------------------------------------
--- Result-type changing arithmetics ---
----------------------------------------

||| Addition of `Fin`s as bounded naturals.
||| The resulting type has the smallest possible bound
||| as illustated by the relations with the `last` function.
public export
(+) : {m, n : Nat} -> Fin m -> Fin (S n) -> Fin (m + n)
(+) FZ y = cast (cong S $ plusCommutative n (pred m)) (weakenN (pred m) y)
(+) (FS x) y = FS (x + y)

||| Multiplication of `Fin`s as bounded naturals.
||| The resulting type has the smallest possible bound
||| as illustated by the relations with the `last` function.
public export
(*) : {m, n : Nat} -> Fin (S m) -> Fin (S n) -> Fin (S (m * n))
(*) FZ _ = FZ
(*) {m = S _} (FS x) y = y + x * y

--- Properties ---

-- Relation between `+` and `*` and their counterparts on `Nat`

export
finToNatPlusHomo : {m, n : Nat} -> (x : Fin m) -> (y : Fin (S n)) ->
                   finToNat (x + y) = finToNat x + finToNat y
finToNatPlusHomo FZ _
  = finToNatQuotient $ transitive
     (castEq _)
     (weakenNNeutral _ _)
finToNatPlusHomo (FS x) y = cong S (finToNatPlusHomo x y)

export
finToNatMultHomo : {m, n : Nat} -> (x : Fin (S m)) -> (y : Fin (S n)) ->
                   finToNat (x * y) = finToNat x * finToNat y
finToNatMultHomo FZ _ = Refl
finToNatMultHomo {m = S _} (FS x) y = Calc $
  |~ finToNat (FS x * y)
  ~~ finToNat (y + x * y)                 ...( Refl )
  ~~ finToNat y + finToNat (x * y)        ...( finToNatPlusHomo y (x * y) )
  ~~ finToNat y + finToNat x * finToNat y ...( cong (finToNat y +) (finToNatMultHomo x y) )
  ~~ finToNat (FS x) * finToNat y         ...( Refl)

-- Relations to `Fin`'s `last`

export
plusPreservesLast : (m, n : Nat) -> Fin.last {n=m} + Fin.last {n} = Fin.last
plusPreservesLast Z     n
  = homoPointwiseIsEqual $ transitive
      (castEq _)
      (weakenNNeutral _ _)
plusPreservesLast (S m) n = cong FS (plusPreservesLast m n)

export
multPreservesLast : (m, n : Nat) -> Fin.last {n=m} * Fin.last {n} = Fin.last
multPreservesLast Z n = Refl
multPreservesLast (S m) n = Calc $
  |~ last + (last * last)
  ~~ last + last          ...( cong (last +) (multPreservesLast m n) )
  ~~ last                 ...( plusPreservesLast n (m * n) )

-- General addition properties

export
plusSuccRightSucc : {m, n : Nat} -> (left : Fin m) -> (right : Fin (S n)) ->
                    FS (left + right) ~~~ left + FS right
plusSuccRightSucc FZ        right = FS $ congCast reflexive
plusSuccRightSucc (FS left) right = FS $ plusSuccRightSucc left right

-- Relations to `Fin`-specific `shift` and `weaken`

export
shiftAsPlus : {m, n : Nat} -> (k : Fin (S m)) ->
              shift n k ~~~ last {n} + k
shiftAsPlus {n=Z}   k =
  symmetric $ transitive (castEq _) (weakenNNeutral _ _)
shiftAsPlus {n=S n} k = FS (shiftAsPlus k)

export
weakenNAsPlusFZ : {m, n : Nat} -> (k : Fin n) ->
                  weakenN m k = k + the (Fin (S m)) FZ
weakenNAsPlusFZ FZ = Refl
weakenNAsPlusFZ (FS k) = cong FS (weakenNAsPlusFZ k)

export
weakenNPlusHomo : {0 m, n : Nat} -> (k : Fin p) ->
                  weakenN n (weakenN m k) ~~~ weakenN (m + n) k
weakenNPlusHomo FZ = FZ
weakenNPlusHomo (FS k) = FS (weakenNPlusHomo k)

export
weakenNOfPlus :
  {m, n : Nat} -> (k : Fin m) -> (l : Fin (S n)) ->
  weakenN w (k + l) ~~~ weakenN w k + l
weakenNOfPlus FZ l
  = transitive (congWeakenN (castEq _))
  $ transitive (weakenNPlusHomo l)
  $ symmetric (castEq _)
weakenNOfPlus (FS k) l = FS (weakenNOfPlus k l)
-- General addition properties (continued)

export
plusZeroLeftNeutral : (k : Fin (S n)) -> FZ + k ~~~ k
plusZeroLeftNeutral k = transitive (castEq _) (weakenNNeutral _ k)

export
congPlusLeft : {m, n, p : Nat} -> {k : Fin m} -> {l : Fin n} ->
               (c : Fin (S p)) -> k ~~~ l -> k + c ~~~ l + c
congPlusLeft c FZ
  = transitive (plusZeroLeftNeutral c)
               (symmetric $ plusZeroLeftNeutral c)
congPlusLeft c (FS prf) = FS (congPlusLeft c prf)

export
plusZeroRightNeutral : (k : Fin m) -> k + FZ ~~~ k
plusZeroRightNeutral FZ = FZ
plusZeroRightNeutral (FS k) = FS (plusZeroRightNeutral k)

export
congPlusRight : {m, n, p : Nat} -> {k : Fin (S n)} -> {l : Fin (S p)} ->
               (c : Fin m) -> k ~~~ l -> c + k ~~~ c + l
congPlusRight c FZ
  = transitive (plusZeroRightNeutral c)
               (symmetric $ plusZeroRightNeutral c)
congPlusRight {n = S _} {p = S _} c (FS prf)
  = transitive (symmetric $ plusSuccRightSucc c _)
  $ transitive (FS $ congPlusRight c prf)
               (plusSuccRightSucc c _)
congPlusRight {p = Z} c (FS prf) impossible

export
plusCommutative : {m, n : Nat} -> (left : Fin (S m)) -> (right : Fin (S n)) ->
                  left + right ~~~ right + left
plusCommutative FZ        right
  = transitive (plusZeroLeftNeutral right)
               (symmetric $ plusZeroRightNeutral right)
plusCommutative {m = S _} (FS left) right
  = transitive (FS (plusCommutative left right))
               (plusSuccRightSucc right left)

export
plusAssociative :
  {m, n, p : Nat} ->
  (left : Fin m) -> (centre : Fin (S n)) -> (right : Fin (S p)) ->
  left + (centre + right) ~~~ (left + centre) + right
plusAssociative FZ centre right
  = transitive (plusZeroLeftNeutral (centre + right))
               (congPlusLeft right (symmetric $ plusZeroLeftNeutral centre))
plusAssociative (FS left) centre right = FS (plusAssociative left centre right)

-------------------------------------------------
--- Splitting operations and their properties ---
-------------------------------------------------

||| Converts `Fin`s that are used as indexes of parts to an index of a sum.
|||
||| For example, if you have a `Vect` that is a concatenation of two `Vect`s and
||| you have an index either in the first or the second of the original `Vect`s,
||| using this function you can get an index in the concatenated one.
public export
indexSum : {m : Nat} -> Either (Fin m) (Fin n) -> Fin (m + n)
indexSum (Left  l) = weakenN n l
indexSum (Right r) = shift m r

||| Extracts an index of the first or the second part from the index of a sum.
|||
||| For example, if you have a `Vect` that is a concatenation of the `Vect`s and
||| you have an index of this `Vect`, you have get an index of either left or right
||| original `Vect` using this function.
public export
splitSum : {m : Nat} -> Fin (m + n) -> Either (Fin m) (Fin n)
splitSum {m=Z}   k      = Right k
splitSum {m=S m} FZ     = Left FZ
splitSum {m=S m} (FS k) = mapFst FS $ splitSum k

||| Calculates the index of a square matrix of size `a * b` by indices of each side.
public export
indexProd : {n : Nat} -> Fin m -> Fin n -> Fin (m * n)
indexProd FZ     = weakenN $ mult (pred m) n
indexProd (FS k) = shift n . indexProd k

||| Splits the index of a square matrix of size `a * b` to indices of each side.
public export
splitProd : {m, n : Nat} -> Fin (m * n) -> (Fin m, Fin n)
splitProd {m=S _} p = case splitSum p of
  Left  k => (FZ, k)
  Right l => mapFst FS $ splitProd l

--- Properties ---

export
indexSumPreservesLast :
  (m, n : Nat) -> indexSum {m} (Right $ Fin.last {n}) ~~~ Fin.last {n=m+n}
indexSumPreservesLast Z     n = reflexive
indexSumPreservesLast (S m) n = FS (shiftLastIsLast m)

export
indexProdPreservesLast : (m, n : Nat) ->
         indexProd (Fin.last {n=m}) (Fin.last {n}) = Fin.last
indexProdPreservesLast Z n = homoPointwiseIsEqual
  $ transitive (weakenNZeroIdentity last)
               (congLast (sym $ plusZeroRightNeutral n))
indexProdPreservesLast (S m) n = Calc $
  |~ indexProd (last {n=S m}) (last {n})
  ~~ FS (shift n (indexProd last last)) ...( Refl )
  ~~ FS (shift n last)                  ...( cong (FS . shift n) (indexProdPreservesLast m n ) )
  ~~ last                               ...( homoPointwiseIsEqual prf )

  where

    prf : shift (S n) (Fin.last {n = n + m * S n}) ~~~ Fin.last {n = n + S (n + m * S n)}
    prf = transitive (shiftLastIsLast (S n))
                     (congLast (plusSuccRightSucc n (n + m * S n)))

export
splitSumOfWeakenN : (k : Fin m) -> splitSum {m} {n} (weakenN n k) = Left k
splitSumOfWeakenN FZ = Refl
splitSumOfWeakenN (FS k) = cong (mapFst FS) $ splitSumOfWeakenN k

export
splitSumOfShift : {m : Nat} -> (k : Fin n) -> splitSum {m} {n} (shift m k) = Right k
splitSumOfShift {m=Z}   k = Refl
splitSumOfShift {m=S m} k = cong (mapFst FS) $ splitSumOfShift k

export
splitOfIndexSumInverse : {m : Nat} -> (e : Either (Fin m) (Fin n)) -> splitSum (indexSum e) = e
splitOfIndexSumInverse (Left l) = splitSumOfWeakenN l
splitOfIndexSumInverse (Right r) = splitSumOfShift r

export
indexOfSplitSumInverse : {m, n : Nat} -> (f : Fin (m + n)) -> indexSum (splitSum {m} {n} f) = f
indexOfSplitSumInverse {m=Z}   f  = Refl
indexOfSplitSumInverse {m=S _} FZ = Refl
indexOfSplitSumInverse {m=S _} (FS f) with (indexOfSplitSumInverse f)
  indexOfSplitSumInverse {m=S _} (FS f) | eq with (splitSum f)
    indexOfSplitSumInverse {m=S _} (FS _) | eq | Left  _ = cong FS eq
    indexOfSplitSumInverse {m=S _} (FS _) | eq | Right _ = cong FS eq


export
splitOfIndexProdInverse : {m : Nat} -> (k : Fin m) -> (l : Fin n) ->
                          splitProd (indexProd k l) = (k, l)
splitOfIndexProdInverse FZ     l
   = rewrite splitSumOfWeakenN {n = mult (pred m) n} l in Refl
splitOfIndexProdInverse (FS k) l
   = rewrite splitSumOfShift {m=n} $ indexProd k l in
     cong (mapFst FS) $ splitOfIndexProdInverse k l

export
indexOfSplitProdInverse : {m, n : Nat} -> (f : Fin (m * n)) ->
                          uncurry (indexProd {m} {n}) (splitProd {m} {n} f) = f
indexOfSplitProdInverse {m = S _} f with (@@ splitSum f)
  indexOfSplitProdInverse {m = S _} f | (Left l ** eq) = rewrite eq in Calc $
    |~ indexSum (Left l)
    ~~ indexSum (splitSum f) ...( cong indexSum (sym eq) )
    ~~ f                     ...( indexOfSplitSumInverse f )
  indexOfSplitProdInverse f | (Right r ** eq) with (@@ splitProd r)
    indexOfSplitProdInverse f | (Right r ** eq) | ((p, q) ** eq2)
      = rewrite eq in rewrite eq2 in Calc $
        |~ indexProd (FS p) q
        ~~ shift n (indexProd p q)                   ...( Refl )
        ~~ shift n (uncurry indexProd (splitProd r)) ...( cong (shift n . uncurry indexProd) (sym eq2) )
        ~~ shift n r                                 ...( cong (shift n) (indexOfSplitProdInverse r) )
        ~~ indexSum (splitSum f)                     ...( sym (cong indexSum eq) )
        ~~ f                                         ...( indexOfSplitSumInverse f )
