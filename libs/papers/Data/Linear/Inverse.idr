||| This module is based on the content of the functional pearl
||| How to Take the Inverse of a Type
||| by Daniel Marshall and Dominic Orchard

module Data.Linear.Inverse

import Data.INTEGER

import Data.Linear
import Data.Linear.LEither
import Data.Linear.LMaybe
import Data.Linear.LVect

import Data.Nat

import Syntax.PreorderReasoning

%default total

||| Inverse is a shorthand for 'multiplicative skew inverse'
export
Inverse : Type -> Type
Inverse a = a -@ ()

export
mkInverse : (a -@ ()) -@ Inverse a
mkInverse f = f

||| And this is the morphism witnessing the multiplicative skew inverse
export
divide : a -@ Inverse a -@ ()
divide x u = u x

export
doubleNegation : a -@ Inverse (Inverse a)
doubleNegation = divide

||| We only use the inverse of a if the LMaybe is actually Just.m
export
maybeNeg : LMaybe a -@ Inverse a -@ LMaybe (Inverse a)
maybeNeg Nothing u = Just u
maybeNeg (Just n) u = divide n u `seq` Nothing

public export
lid : a -@ a
lid x = x

public export
lcompose : (b -@ c) -@ (a -@ b) -@ (a -@ c)
lcompose g f = \ 1 x => g (f x)

public export
comap : (b -@ a) -@ Inverse a -@ Inverse b
comap f u = lcompose u f

export
comapId : (u : Inverse a) -> Inverse.comap Inverse.lid u === Inverse.lid u
comapId u = Refl

export
comapComp : (u : Inverse a) ->
  Inverse.comap (lcompose g f) u
  === lcompose (Inverse.comap f) (Inverse.comap g) u
comapComp u = Refl

export
munit : () -@ Inverse ()
munit u = u `seq` lid

export
mmult : Inverse a -@ Inverse b -@ Inverse (LPair a b)
mmult ua ub (a # b) = divide a ua `seq` divide b ub

public export
Pow : Type -> INTEGER -> Type
Pow a Z = ()
Pow a (PS n) = LVect (S n) a
Pow a (NS n) = LVect (S n) (Inverse a)

public export
zip : {n : INTEGER} -> Pow a n -@ Pow b n -@ Pow (LPair a b) n
zip {n = Z} as bs = as `seq` bs
zip {n = (PS k)} as bs = zip as bs
zip {n = (NS k)} as bs = mmult <$> as <*> bs

export
powPositiveL : (m, n : Nat) -> Pow a (cast $ m + n) -@
               LPair (Pow a (cast m)) (Pow a (cast n))
powPositiveL Z n as = (() # as)
powPositiveL 1 Z [a] = ([a] # ())
powPositiveL 1 (S n) (a :: as) = ([a] # as)
powPositiveL (S m@(S _)) n (a :: as)
  = let (xs # ys) = powPositiveL m n as in (a :: xs # ys)

export
powPositiveR : (m, n : Nat) -> Pow a (cast m) -@ Pow a (cast n) -@
           Pow a (cast $ m + n)
powPositiveR 0 n xs ys = xs `seq` ys
powPositiveR 1 0 xs ys = ys `seq` xs
powPositiveR 1 (S n) [a] ys = a :: ys
powPositiveR (S m@(S _)) n (x :: xs) ys = x :: powPositiveR m n xs ys

export
powNegateL : (m : Nat) -> Pow a (- cast m) -> Pow (Inverse a) (cast m)
powNegateL Z as = as
powNegateL (S m) as = as

export
powNegateR : (m : Nat) -> Pow (Inverse a) (cast m) -> Pow a (- cast m)
powNegateR Z as = as
powNegateR (S m) as = as

export
powNegativeL : (m, n : Nat) -> Pow a (- cast (m + n)) -@
            LPair (Pow a (- cast m)) (Pow a (- cast n))
powNegativeL Z n as = (() # as)
powNegativeL 1 Z [a] = ([a] # ())
powNegativeL 1 (S n) (a :: as) = ([a] # as)
powNegativeL (S m@(S _)) n (a :: as)
  = let (xs # ys) = powNegativeL m n as in (a :: xs # ys)

export
powNegativeR : (m, n : Nat) -> Pow a (- cast m) -@ Pow a (- cast n) -@
           Pow a (- cast (m + n))
powNegativeR 0 n xs ys = xs `seq` ys
powNegativeR 1 0 xs ys = ys `seq` xs
powNegativeR 1 (S n) [a] ys = a :: ys
powNegativeR (S m@(S _)) n (x :: xs) ys = x :: powNegativeR m n xs ys

export
powAnnihilate : (m : Nat) -> Pow a (cast m) -@ Pow a (- cast m) -@ ()
powAnnihilate 0         pos neg = pos `seq` neg
powAnnihilate 1         [x] [u] = u x
powAnnihilate (S (S k)) (x :: pos) (u :: neg)
  = u x `seq` powAnnihilate (S k) pos neg

powMinusAux : (m, n : Nat) -> CmpNat m n ->
  Pow a (cast m) -@ Pow a (- cast n) -@ Pow a (cast m - cast n)
powMinusAux m (m + S n) (CmpLT n) pos neg
  = let (neg1 # neg2) = powNegativeL m (S n) neg in
    powAnnihilate m pos neg1 `seq` replace {p = Pow a} eq neg2

  where

  eq : NS n === cast m - cast (m + S n)
  eq = sym $ Calc $
     |~ cast m - cast (m + S n)
     ~~ cast m - (cast m + cast (S n))
        ...( cong (cast m -) (castPlus m (S n)) )
     ~~ cast m + (- cast m - cast (S n))
        ...( cong (cast m +) (negatePlus (cast m) (cast (S n))) )
     ~~ (cast m - cast m) - cast (S n)
        ...( plusAssociative (cast m) (- cast m) (- cast (S n)) )
     ~~ - cast (S n)
        ...( cong (+ - cast (S n)) (plusInverse (cast m)) )

powMinusAux m m CmpEQ pos neg
  = rewrite plusInverse (cast m) in
    powAnnihilate (cast m) pos neg
powMinusAux (_ + S m) n (CmpGT m) pos neg
  = let (pos1 # pos2) = powPositiveL n (S m) pos in
    powAnnihilate n pos1 neg `seq` replace {p = Pow a} eq pos2

  where

  eq : PS m === cast (n + S m) - cast n
  eq = sym $ Calc $
    |~ cast (n + S m) - cast n
    ~~ cast n + cast (S m) - cast n
      ...( cong (+ - cast n) (castPlus n (S m)) )
    ~~ cast n + (cast (S m) - cast n)
      ...( sym (plusAssociative (cast n) (cast (S m)) (- cast n)) )
    ~~ cast n + (- cast n + cast (S m))
      ...( cong (cast n +) (plusCommutative (cast (S m)) (- cast n)) )
    ~~ (cast n - cast n) + cast (S m)
      ...( plusAssociative (cast n) (- cast n) (cast (S m)) )
    ~~ cast (S m)
      ...( cong (+ cast (S m)) (plusInverse (cast n)) )

export
powMinus : (m, n : Nat) ->
  Pow a (cast m) -@ Pow a (- cast n) -@ Pow a (cast m - cast n)
powMinus m n = powMinusAux m n (cmp m n)
