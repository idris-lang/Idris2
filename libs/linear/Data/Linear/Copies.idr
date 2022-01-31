module Data.Linear.Copies

import Data.Linear.Notation
import Data.Nat

infix 1 `Copies`

||| Carries multiple linear copies of the same value. Usage: m `Copies` x
||| reads as "m copies of value x". This data structure is necessary to implement
||| algorithms that rely on linearity but also interact with Nat indicies, like
||| Vect and Fin.
||| This datastructure can be found in the paper "How to Take the Inverse of a Type" by
||| Daniel Marshall and Dominic Orchard where it's described as an exponent operator
public export
data Copies : Nat -> (0 x : a) -> Type where
  Nil : Copies Z x
  (::) : (1 x : a) -> (1 copies : Copies n x) -> Copies (S n) x

||| Split copies into two
export
splitAt : (1 m : Nat) -> Copies (m + n) x -@ LPair (Copies m x) (Copies n x)
splitAt Z xs = ([] # xs)
splitAt (S m) (x :: xs) = let (ys # zs) = splitAt m xs in (x :: ys # zs)

||| Combine multiple copies into one
export
(++) : Copies m x -@ Copies n x -@ Copies (m + n) x
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

||| Copies of pairs are like pairs of copies
export
unzip : Copies m (Builtin.(#) x y) -@ LPair (Copies m x) (Copies m y)
unzip [] = [] # []
unzip ((x # y) :: xys) = let (xs # ys) = unzip xys in (x :: xs # y :: ys)

-- Copies is a bit of an applicative
export
pure : {1 n : Nat} -> (x : a) -> Copies n x
pure {n = Z} x = []
pure {n = S n} x = x :: pure x

export
(<*>) : Copies {a = a -@ b} m f -@ Copies m x -@ Copies m (f x)
[] <*> [] = []
(f :: fs) <*> (x :: xs) = f x :: (fs <*> xs)

||| Note that this is not quite `pure f <*> xs` because we don't actually
||| need to know `m` to be able to define `(<$>)` as we can proceed by
||| induction on xs.
export
(<$>) : (f : a -@ b) -> Copies m x -@ Copies m (f x)
f <$> [] = []
f <$> (x :: xs) = f x :: (f <$> xs)

||| Combine copies of two values into a pair of copies
export
zip : Copies m x -@ Copies m y -@ Copies m (Builtin.(#) x y)
zip as bs = (#) <$> as <*> bs

