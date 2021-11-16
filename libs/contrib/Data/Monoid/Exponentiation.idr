module Data.Monoid.Exponentiation

import Data.Nat.Views
import Syntax.PreorderReasoning

%default total

------------------------------------------------------------------------
-- Implementations

public export
linear : Monoid a => a -> Nat -> a
linear v Z = neutral
linear v (S k) = v <+> linear v k

public export
modularRec : Monoid a => a -> HalfRec n -> a
modularRec v HalfRecZ = neutral
modularRec v (HalfRecEven _ acc) = let e = modularRec v acc in e <+> e
modularRec v (HalfRecOdd _ acc) = let e = modularRec v acc in v <+> e <+> e

public export
modular : Monoid a => a -> Nat -> a
modular v n = modularRec v (halfRec n)

infixr 10 ^
public export
(^) : Num a => a -> Nat -> a
(^) = modular @{Multiplicative}

------------------------------------------------------------------------
-- Properties

-- Not using `MonoidV` because it's cursed
export
linearPlusHomo : (mon : Monoid a) =>
  -- good monoid
  (opAssoc : {0 x, y, z : a} -> ((x <+> y) <+> z) === (x <+> (y <+> z))) ->
  (neutralL : {0 x : a} -> (neutral @{mon} <+> x) === x) ->
  -- result
  (v : a) -> {m, n : Nat} ->
  (linear v m <+> linear v n) === linear v (m + n)
linearPlusHomo opAssoc neutralL v = go m where

  go : (m : Nat) -> (linear v m <+> linear v n) === linear v (m + n)
  go Z = neutralL
  go (S m) = Calc $
    |~ (v <+> linear v m) <+> linear v n
    ~~ v <+> (linear v m <+> linear v n) ...( opAssoc )
    ~~ v <+> (linear v (m + n))          ...( cong (v <+>) (go m) )

export
modularRecCorrect : (mon : Monoid a) =>
    -- good monoid
  (opAssoc : {0 x, y, z : a} -> ((x <+> y) <+> z) === (x <+> (y <+> z))) ->
  (neutralL : {0 x : a} -> (neutral @{mon} <+> x) === x) ->
  -- result
  (v : a) -> {n : Nat} -> (p : HalfRec n) ->
  modularRec v p === linear v n
modularRecCorrect opAssoc neutralL v acc = go acc where

  aux : {m, n : Nat} -> (linear v m <+> linear v n) === linear v (m + n)
  aux = linearPlusHomo opAssoc neutralL v

  go : {n : Nat} -> (p : HalfRec n) -> modularRec v p === linear v n
  go HalfRecZ = Refl
  go (HalfRecEven k acc) = rewrite go acc in aux
  go (HalfRecOdd k acc) = rewrite go acc in Calc $
    |~ (v <+> linear v k) <+> linear v k
    ~~ v <+> (linear v k <+> linear v k)  ...( opAssoc )
    ~~ v <+> (linear v (k + k))           ...( cong (v <+>) aux )

export
modularCorrect : (mon : Monoid a) =>
    -- good monoid
  (opAssoc : {0 x, y, z : a} -> ((x <+> y) <+> z) === (x <+> (y <+> z))) ->
  (neutralL : {0 x : a} -> (neutral @{mon} <+> x) === x) ->
  -- result
  (v : a) -> {n : Nat} -> modular v n === linear v n
modularCorrect opAssoc neutralL v
  = modularRecCorrect opAssoc neutralL v (halfRec n)
