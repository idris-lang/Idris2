||| Result-type changing `Fin` arithmetics
module Data.Fin.Arith

import public Data.Fin

import Syntax.PreorderReasoning

%default total

||| Addition of `Fin`s as bounded naturals.
||| The resulting type has the smallest possible bound
||| as illustrated by the relations with the `last` function.
public export
(+) : {m, n : Nat} -> Fin m -> Fin (S n) -> Fin (m + n)
(+) FZ y = coerce (cong S $ plusCommutative n (pred m)) (weakenN (pred m) y)
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
     (coerceEq _)
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
  ~~ finToNat (FS x) * finToNat y         ...( Refl )

-- Relations to `Fin`'s `last`

export
plusPreservesLast : (m, n : Nat) -> Fin.last {n=m} + Fin.last {n} = Fin.last
plusPreservesLast Z     n
  = homoPointwiseIsEqual $ transitive
      (coerceEq _)
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
plusSuccRightSucc FZ        right = FS $ congCoerce reflexive
plusSuccRightSucc (FS left) right = FS $ plusSuccRightSucc left right

-- Relations to `Fin`-specific `shift` and `weaken`

export
shiftAsPlus : {m, n : Nat} -> (k : Fin (S m)) ->
              shift n k ~~~ last {n} + k
shiftAsPlus {n=Z}   k =
  symmetric $ transitive (coerceEq _) (weakenNNeutral _ _)
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
  = transitive (congWeakenN (coerceEq _))
  $ transitive (weakenNPlusHomo l)
  $ symmetric (coerceEq _)
weakenNOfPlus (FS k) l = FS (weakenNOfPlus k l)
-- General addition properties (continued)

export
plusZeroLeftNeutral : (k : Fin (S n)) -> FZ + k ~~~ k
plusZeroLeftNeutral k = transitive (coerceEq _) (weakenNNeutral _ k)

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
