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

export
plusZeroRightNeutral : (m : INTEGER) -> m + 0 === m
plusZeroRightNeutral Z = Refl
plusZeroRightNeutral (PS k) = Refl
plusZeroRightNeutral (NS k) = Refl

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
castPlus : (m, n : Nat) -> the INTEGER (cast (m + n)) = cast m + cast n
castPlus 0     n     = Refl
castPlus (S m) 0     = cong PS (plusZeroRightNeutral m)
castPlus (S m) (S n) = cong PS (sym $ plusSuccRightSucc m n)

public export
Neg INTEGER where
  negate Z = Z
  negate (PS n) = NS n
  negate (NS n) = PS n

  m - n = add m (negate n)

export
unfoldPS : (m : Nat) -> PS m === 1 + cast m
unfoldPS Z = Refl
unfoldPS (S m) = Refl

export
unfoldNS : (m : Nat) -> NS m === - 1 - cast m
unfoldNS Z = Refl
unfoldNS (S m) = Refl

export
difference : (m, n : Nat) -> INTEGER
difference 0 n = - cast n
difference m 0 = cast m
difference (S m) (S n) = difference m n

export
differenceZeroRight : (n : Nat) -> difference n 0 === cast n
differenceZeroRight 0 = Refl
differenceZeroRight (S k) = Refl

export
minusSuccSucc : (m, n : Nat) ->
  the INTEGER (cast (S m) - cast (S n)) === cast m - cast n
minusSuccSucc 0 0 = Refl
minusSuccSucc 0 (S n) = cong NS (minusZeroRight n)
minusSuccSucc (S m) 0 = cong PS (minusZeroRight m)
minusSuccSucc (S m) (S n) with (compare m n)
  _ | LT = Refl
  _ | EQ = Refl
  _ | GT = Refl

export
unfoldDifference : (m, n : Nat) -> difference m n === cast m - cast n
unfoldDifference 0 n = Refl
unfoldDifference m 0 = Calc $
  |~ difference m 0
  ~~ cast m     ...( differenceZeroRight m )
  ~~ cast m + 0 ...( sym (plusZeroRightNeutral $ cast m) )
unfoldDifference (S m) (S n) = Calc $
  |~ difference m n
  ~~ cast m - cast n         ...( unfoldDifference m n )
  ~~ cast (S m) - cast (S n) ...( sym (minusSuccSucc m n) )

export
negateInvolutive : (m : INTEGER) -> - - m === m
negateInvolutive Z = Refl
negateInvolutive (PS k) = Refl
negateInvolutive (NS k) = Refl

export
negatePlus : (m, n : INTEGER) -> - (m + n) === - m + - n
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
negateDifference : (m, n : Nat) -> - difference m n === difference n m
negateDifference 0 n = Calc $
  |~ - - cast n
  ~~ cast n         ...( negateInvolutive (cast n) )
  ~~ difference n 0 ...( sym (differenceZeroRight n) )
negateDifference m 0 = cong negate (differenceZeroRight m)
negateDifference (S m) (S n) = negateDifference m n

plusNatDifferenceLeft : (m, n, p : Nat) ->
  cast m + difference n p === difference (m + n) p
plusNatDifferenceLeft m 0 p = Calc $
  |~ cast m - cast p
  ~~ difference m p
    ...( sym (unfoldDifference m p) )
  ~~ difference (m + 0) p
    ...( cong (flip difference p) (sym $ plusZeroRightNeutral m) )
plusNatDifferenceLeft m (S n) p = Calc $
  |~ cast m + difference (S n) p
  ~~ PS m + difference n p
     ...( sym (aux n p m) )
  ~~ difference (S m + n) p
     ...( plusNatDifferenceLeft (S m) n p )
  ~~ difference (m + S n) p
     ...( cong (flip difference p) (plusSuccRightSucc m n) )

 where

  aux : (m, n, p : Nat) -> PS p + difference m n === cast p + difference (S m) n
  aux 0 0 p = Calc $
    |~ PS p
    ~~ 1 + cast p ...( unfoldPS p )
    ~~ cast p + 1 ...( plusCommutative 1 (cast p) )
  aux 0 (S k) p = Calc $
    |~ PS p + NS k
    ~~ difference (S p) (S k) ...( sym (unfoldDifference (S p) (S k)) )
    ~~ difference p k         ...( Refl )
    ~~ cast p - cast k        ...( unfoldDifference p k )
  aux (S k) 0 p = sym $ Calc $
    |~ cast p + PS (S k)
    ~~ cast (p + S (S k)) ...( sym (castPlus p (S (S k))) )
    ~~ cast (S (p + S k)) ...( cong cast (sym $ plusSuccRightSucc p (S k)) )
    ~~ cast (S (S p + k)) ...( cong PS (sym $ plusSuccRightSucc p k) )
  aux (S k) (S j) p = aux k j p

minusNatDifferenceRight : (m, n, p : Nat) ->
  - cast m + difference n p === difference n (m + p)
minusNatDifferenceRight m n p = Calc $
  |~ - cast m + difference n p
  ~~ - cast m - - difference n p
     ...( cong (- cast m +) (sym $ negateInvolutive ?) )
  ~~ - (cast m - difference n p)
     ...( sym (negatePlus (cast m) (- difference n p)) )
  ~~ - (cast m + difference p n)
     ...( cong (negate . (cast m +)) (negateDifference n p) )
  ~~ - (difference (m + p) n)
     ...( cong negate (plusNatDifferenceLeft m p n) )
  ~~ - - difference n (m + p)
     ...( cong negate (sym $ negateDifference n (m + p)) )
  ~~ difference n (m + p)
     ...( negateInvolutive ? )


export
minusZeroRight : (m : INTEGER) -> m - 0 === m
minusZeroRight = plusZeroRightNeutral


export
plusInverse : (m : INTEGER) -> m - m === Z
plusInverse Z      = Refl
plusInverse (PS k) = rewrite compareNatDiag k in Refl
plusInverse (NS k) = rewrite compareNatDiag k in Refl

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
plusAssociative (PS k) (PS j) (NS i) = Calc $
  |~ PS k + (PS j - PS i)
  ~~ PS k + difference (S j) (S i)
     ...( cong (PS k +) (sym $ unfoldDifference (S j) (S i)) )
  ~~ difference (S k + S j) (S i)
     ...( plusNatDifferenceLeft (S k) (S j) (S i) )
  ~~ difference (S (S (k + j))) (S i)
     ...( cong (flip difference (S i)) (sym $ plusSuccRightSucc (S k) j) )
  ~~ PS k + PS j - PS i
     ...( unfoldDifference (S (S (k + j))) (S i) )
plusAssociative (PS k) (NS j) (PS i) = Calc $
  |~ PS k + (NS j + PS i)
  ~~ PS k + (PS i + NS j)
     ...( cong (PS k +) (plusCommutative (NS j) (PS i)) )
  ~~ PS k + difference (S i) (S j)
     ...( cong (PS k +) (sym $ unfoldDifference (S i) (S j)) )
  ~~ difference (S k + S i) (S j)
     ...( plusNatDifferenceLeft (S k) (S i) (S j) )
  ~~ difference (S i + S k) (S j)
     ...( cong (flip difference (S j)) (plusCommutative (S k) (S i)) )
  ~~ PS i + difference (S k) (S j)
     ...( sym (plusNatDifferenceLeft (S i) (S k) (S j)) )
  ~~ difference (S k) (S j) + PS i
     ...( plusCommutative (PS i) (difference (S k) (S j)) )
  ~~ PS k + NS j + PS i
     ...( cong (+ PS i) (unfoldDifference (S k) (S j)) )
plusAssociative (PS k) (NS j) (NS i) = Calc $
  |~ PS k + NS (S j + i)
  ~~ difference (S k) (S (S j + i))
     ...( sym (unfoldDifference (S k) (S (S j + i))) )
  ~~ difference (S k) (S i + S j)
     ...( cong (difference k) (plusCommutative (S j) i) )
  ~~ NS i + difference (S k) (S j)
     ...( sym (minusNatDifferenceRight (S i) (S k) (S j)) )
  ~~ difference (S k) (S j) + NS i
     ...( plusCommutative (NS i) (difference (S k) (S j)) )
  ~~ (PS k + NS j) + NS i
     ...( cong (+ NS i) (unfoldDifference (S k) (S j)) )
plusAssociative (NS k) (PS j) (PS i) = Calc $
  |~ NS k + (PS j + PS i)
  ~~ (PS j + PS i) + NS k
     ...( plusCommutative (NS k) (PS j + PS i) )
  ~~ difference (S (S (j + i))) (S k)
     ...( sym (unfoldDifference (S (S (j + i))) (S k)) )
  ~~ difference (S i + S j) (S k)
     ...( cong (flip difference k) (plusCommutative (S j) i) )
  ~~ PS i + difference (S j) (S k)
     ...( sym (plusNatDifferenceLeft (S i) (S j) (S k)) )
  ~~ difference (S j) (S k) + PS i
     ...( plusCommutative (PS i) (difference (S j) (S k)) )
  ~~ (PS j + NS k) + PS i
     ...( cong (+ PS i) (unfoldDifference (S j) (S k)) )
  ~~ (NS k + PS j) + PS i
     ...( cong (+ PS i) (plusCommutative (PS j) (NS k)) )
plusAssociative (NS k) (PS j) (NS i) = Calc $
  |~ NS k + (PS j + NS i)
  ~~ NS k + difference (S j) (S i)
     ...( cong (NS k +) (sym $ unfoldDifference (S j) (S i)) )
  ~~ difference (S j) (S k + S i)
     ...( minusNatDifferenceRight (S k) (S j) (S i) )
  ~~ difference (S j) (S i + S k)
     ...( cong (difference (S j)) (plusCommutative (S k) (S i)) )
  ~~ NS i + difference (S j) (S k)
     ...( sym (minusNatDifferenceRight (S i) (S j) (S k)) )
  ~~ difference (S j) (S k) + NS i
     ...( plusCommutative (NS i) (difference (S j) (S k)) )
  ~~ (PS j + NS k) + NS i
     ...( cong (+ NS i) (unfoldDifference (S j) (S k)) )
  ~~ (NS k + PS j) + NS i
     ...( cong (+ NS i) (plusCommutative (PS j) (NS k)) )
plusAssociative (NS k) (NS j) (PS i) = Calc $
  |~ NS k + (NS j + PS i)
  ~~ NS k + (PS i + NS j)
     ...( cong (NS k +) (plusCommutative (NS j) (PS i)) )
  ~~ NS k + difference (S i) (S j)
     ...( cong (NS k +) (sym $ unfoldDifference (S i) (S j)) )
  ~~ difference (S i) (S k + S j)
     ...( minusNatDifferenceRight (S k) (S i) (S j) )
  ~~ difference (S i) (S (S (k + j)))
     ...( cong (difference i) (sym $ plusSuccRightSucc k j) )
  ~~ PS i + (NS k + NS j)
     ...( unfoldDifference (S i) (S (S (k + j))) )
  ~~ (NS k + NS j) + PS i
     ...( plusCommutative (PS i) (NS k + NS j) )
plusAssociative (NS k) (NS j) (NS i) = cong (NS . S) $ Calc $
  |~ k + S (j + i)
  ~~ S (k + (j + i)) ...( sym (plusSuccRightSucc k (j + i)) )
  ~~ S ((k + j) + i) ...( cong S (plusAssociative k j i) )
