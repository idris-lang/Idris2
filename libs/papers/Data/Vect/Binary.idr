||| The content of this file is taken from the paper
||| Heterogeneous Binary Random-access lists

module Data.Vect.Binary

import Data.Binary.Digit
import Data.Binary
import Data.IMaybe
import Data.Nat
import Data.Nat.Exponentiation
import Data.Tree.Perfect

%default total

public export
data BVect : Nat -> Bin -> Type -> Type where
  Nil  : BVect n [] a
  (::) : IMaybe (isI b) (Tree n a) -> BVect (S n) bs a -> BVect n (b :: bs) a

public export
data Path : Nat -> Bin -> Type where
  Here  : Path n -> Path n (I :: bs)
  There : Path (S n) bs -> Path n (b :: bs)

public export
zero : {bs : Bin} -> {n : Nat} -> Path n (suc bs)
zero {bs} = case bs of
  [] => Here (fromNat 0 n (ltePow2 {m = n}))
  (O :: bs) => Here (fromNat 0 n (ltePow2 {m = n}))
  (I :: bs) => There zero

public export
lookup : BVect n bs a -> Path n bs -> a
lookup (hd :: _) (Here p) = lookup (fromJust hd) p
lookup (_ :: tl) (There p) = lookup tl p

public export
cons : {bs : _} -> Tree n a -> BVect n bs a -> BVect n (suc bs) a
cons t [] = [Just t]
cons {bs = b :: _} t (u :: us) = case b of
  I => Nothing :: cons (Node t (fromJust u)) us
  O => Just t :: us
