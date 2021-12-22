module Data.Linear.Pow

import Data.Linear.Notation

data Pow : (0 x : a) -> Nat -> Type where
  Nil : Pow x Z
  (::) : (1 x : a) -> Pow x n -@ Pow x (S n)

splitAt : (1 m : Nat) -> Pow x (m + n) -@ LPair (Pow x m) (Pow x n)
splitAt Z xs = ([] # xs)
splitAt (S m) (x :: xs) = let (ys # zs) = splitAt m xs in (x :: ys # zs)

(++) : Pow x m -@ Pow x n -@ Pow x (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

unzip : Pow (Builtin.(#) x y) m -@ LPair (Pow x m) (Pow y m)
unzip [] = [] # []
unzip ((x # y) :: xys) = let (xs # ys) = unzip xys in (x :: xs # y :: ys)

-- Pow is a bit of an applicative

pure : {1 n : Nat} -> (x : a) -> Pow x n
pure {n = Z} x = []
pure {n = S n} x = x :: pure x

(<*>) : Pow {a = a -@ b} f m -@ Pow x m -@ Pow (f x) m
[] <*> [] = []
(f :: fs) <*> (x :: xs) = f x :: (fs <*> xs)

||| Note that this is not quite `pure f <*> xs` because we don't actually
||| need to know `m` to be able to define `(<$>)` as we can proceed by
||| induction on xs.
(<$>) : (f : a -@ b) -> Pow x m -@ Pow (f x) m
f <$> [] = []
f <$> (x :: xs) = f x :: (f <$> xs)

zip : Pow x m -@ Pow y m -@ Pow (Builtin.(#) x y) m
zip as bs = (#) <$> as <*> bs
