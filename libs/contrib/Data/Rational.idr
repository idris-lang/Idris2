module Data.Rational

import Data.Nat.Factor

%default total

public export
data Nat1 : Type where
   S : Nat -> Nat1

export
Cast Nat1 Integer where
   cast (S n) = (natToInteger n) + 1

mult : Nat1 -> Nat1 -> Nat1
mult (S m) (S n) = S (m + n + m * n)

toNat_notbothzero : Nat1 -> Nat
toNat_notbothzero (S n) = S n

fromNat_coerce : Nat -> Nat1
fromNat_coerce Z = S Z
fromNat_coerce (S n) = S n

public export
record Rational where
   constructor RatioOf
   numerator : Integer
   denominator : Nat1


-- TODO: inline all this as prim__
toUnsigned : Integer -> (Nat, Bool)
toUnsigned n = if n < 0 then (cast n, False) else (cast (negate n), True)

fromUnsigned : (Nat, Bool) -> Integer
fromUnsigned (n, False) = cast n
fromUnsigned (n, True) = negate (cast n)

lcd : Nat -> Nat -> Nat
lcd 0 _ = 1
lcd _ 0 = 1
lcd m 1 = 1
lcd 1 n = 1
lcd m n = if m > n then lcd n (assert_smaller m (m `minus` n)) else lcd n m

divide : Nat -> Nat -> Nat
divide m n = fromInteger $ (natToInteger m) `div` (natToInteger n)

gcd_div : (Nat, Nat) -> (Nat, Nat)
gcd_div (m, n) = do
   let l = lcd m n
   (m `divide` l, n `divide` l)

simplify : Rational -> Rational
simplify (RatioOf m n) = do
   let n' = toNat_notbothzero n
   let (m', is_negative) = toUnsigned m
   let (n'', m'') = gcd_div (n', m')
   RatioOf (fromUnsigned (m'', is_negative)) (fromNat_coerce n'')
-- inline this (end)


export
Num Rational where
   (+) (RatioOf m n) (RatioOf m' n') =
      let 
         numer = (m * (cast n')) + (m' * (cast n))
         denom = n `mult` n'
      in
         -- TODO: produce better algorithm to simplify inplace
         simplify (RatioOf numer denom)

   (*) (RatioOf m n) (RatioOf m' n') =
      let
         numer = m * m'
         denom = n `mult` n'
      in
         -- TODO: produce better algorithm to simplify inplace
         simplify (RatioOf numer denom)
      
   fromInteger n = RatioOf n (S 0)

export
Neg Rational where
   negate (RatioOf m n) = RatioOf (negate m) n
   (-) m n = (+) m (negate n)

export
Abs Rational where
   abs (RatioOf m n) = RatioOf (abs m) n
