module Data.INTEGER

import Data.Nat

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
addInverse : (m : INTEGER) -> add m (negate m) === Z
addInverse Z      = Refl
addInverse (PS k) = rewrite compareNatDiag k in Refl
addInverse (NS k) = rewrite compareNatDiag k in Refl
