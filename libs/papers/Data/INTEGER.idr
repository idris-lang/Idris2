module Data.INTEGER

import Data.Nat
import Syntax.PreorderReasoning

%default total

public export
data INTEGER : Type where
  Z : INTEGER
  PS : Nat -> INTEGER
  NS : Nat -> INTEGER

public export
Cast Nat INTEGER where
  cast Z = Z
  cast (S n) = PS n

public export
Cast Integer INTEGER where
  cast i = case compare 0 i of
    LT => PS (cast (i - 1))
    EQ => Z
    GT => NS (cast (negate i - 1))

public export
Cast INTEGER Integer where
  cast Z = 0
  cast (PS n) = 1 + cast n
  cast (NS n) = negate (1 + cast n)

public export
Show INTEGER where
  show = show . cast {to = Integer}

public export
add : INTEGER -> INTEGER -> INTEGER
add Z n = n
add m Z = m
add (PS m) (PS n) = PS (S (m + n))
add (NS m) (NS n) = NS (S (m + n))
add (PS m) (NS n) = case compare m n of
  LT => NS (minus n (S m)) -- 1+m-1-n = 1+(m-n-1)
  EQ => Z
  GT => PS (minus m (S n))
add (NS n) (PS m) = case compare m n of
  LT => NS (minus n (S m))
  EQ => Z
  GT => PS (minus m (S n))

public export
mult : INTEGER -> INTEGER -> INTEGER
mult Z n = Z
mult m Z = Z
mult (PS m) (PS n) = PS (m * n + m + n)
mult (NS m) (NS n) = PS (m * n + m + n)
mult (PS m) (NS n) = NS (m * n + m + n)
mult (NS m) (PS n) = NS (m * n + m + n)

public export
Num INTEGER where
  fromInteger = cast
  (+) = add
  (*) = mult

public export
Neg INTEGER where
  negate Z = Z
  negate (PS n) = NS n
  negate (NS n) = PS n

  m - n = add m (negate n)

export
castPlus : (m, n : Nat) -> the INTEGER (cast (m + n)) = cast m + cast n
castPlus 0     n     = Refl
castPlus (S m) 0     = cong PS (plusZeroRightNeutral m)
castPlus (S m) (S n) = cong PS (sym $ plusSuccRightSucc m n)

export
plusZeroRightNeutral : (m : INTEGER) -> m + 0 === m
plusZeroRightNeutral Z = Refl
plusZeroRightNeutral (PS k) = Refl
plusZeroRightNeutral (NS k) = Refl

export
negatePlus : (m, n : INTEGER) -> negate (m + n) === negate m + negate n
negatePlus Z n = Refl
negatePlus (PS k) Z = Refl
negatePlus (NS k) Z = Refl
negatePlus (PS k) (PS j) = Refl
negatePlus (PS k) (NS j) with (compare k j) proof eq
  _ | LT = rewrite compareNatFlip k j in rewrite eq in Refl
  _ | EQ = rewrite compareNatFlip k j in rewrite eq in Refl
  _ | GT = rewrite compareNatFlip k j in rewrite eq in Refl
negatePlus (NS k) (PS j) with (compare k j) proof eq
  _ | LT = rewrite compareNatFlip k j in rewrite eq in Refl
  _ | EQ = rewrite compareNatFlip k j in rewrite eq in Refl
  _ | GT = rewrite compareNatFlip k j in rewrite eq in Refl
negatePlus (NS k) (NS j) = Refl

export
plusInverse : (m : INTEGER) -> m + negate m === Z
plusInverse Z      = Refl
plusInverse (PS k) = rewrite compareNatDiag k in Refl
plusInverse (NS k) = rewrite compareNatDiag k in Refl

export
plusCommutative : (m, n : INTEGER) -> m + n === n + m
plusCommutative Z n = sym $ plusZeroRightNeutral n
plusCommutative m Z = plusZeroRightNeutral m
plusCommutative (PS k) (PS j) = cong (PS . S) (plusCommutative k j)
plusCommutative (NS k) (NS j) = cong (NS . S) (plusCommutative k j)
plusCommutative (PS k) (NS j) with (compare k j)
  _ | LT = Refl
  _ | EQ = Refl
  _ | GT = Refl
plusCommutative (NS k) (PS j) with (compare j k)
  _ | LT = Refl
  _ | EQ = Refl
  _ | GT = Refl

export
plusAssociative : (m, n, p : INTEGER) -> m + (n + p) === (m + n) + p
plusAssociative Z n p = Refl
plusAssociative m Z p = cong (+ p) (sym $ plusZeroRightNeutral m)
plusAssociative m n Z = Calc $
  |~ m + (n + Z)
  ~~ m + n     ...( cong (m +) (plusZeroRightNeutral n) )
  ~~ m + n + Z ...( sym $ plusZeroRightNeutral (m + n) )
plusAssociative (PS k) (PS j) (PS i) = cong (PS . S) $ Calc $
  |~ k + S (j + i)
  ~~ S (k + (j + i)) ...( sym (plusSuccRightSucc k (j + i)) )
  ~~ S ((k + j) + i) ...( cong S (plusAssociative k j i) )
plusAssociative (PS k) (PS j) (NS i) = ?a_2
plusAssociative (PS k) (NS j) (PS i) = ?a_7
plusAssociative (PS k) (NS j) (NS i) = ?a_8
plusAssociative (NS k) (PS j) (PS i) = ?a_6
plusAssociative (NS k) (PS j) (NS i) = ?a_9
plusAssociative (NS k) (NS j) (PS i) = ?b_1
plusAssociative (NS k) (NS j) (NS i) = cong (NS . S) $ Calc $
  |~ k + S (j + i)
  ~~ S (k + (j + i)) ...( sym (plusSuccRightSucc k (j + i)) )
  ~~ S ((k + j) + i) ...( cong S (plusAssociative k j i) )
