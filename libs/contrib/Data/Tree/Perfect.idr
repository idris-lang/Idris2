module Data.Tree.Perfect

import Decidable.Order
import Decidable.Order.Strict
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Strict
import Data.Nat.Order.Properties
import Data.DPair
import Syntax.WithProof

%default total

public export
data Tree : Nat -> Type -> Type where
  Leaf : a -> Tree Z a
  Node : Tree n a -> Tree n a -> Tree (S n) a

public export
Functor (Tree n) where
  map f (Leaf a) = Leaf (f a)
  map f (Node l r) = Node (map f l) (map f r)

public export
data Path : Nat -> Type where
  Here  : Path Z
  Left  : Path n -> Path (S n)
  Right : Path n -> Path (S n)

infixl 10 ^

public export
(^) : Num a => a -> Nat -> a
m ^ Z = 1
m ^ S n = let k = m ^ n in k + k

export
lteExp : {m : Nat} -> LTE 1 (2 ^ m)
lteExp {m = Z} = lteRefl
lteExp {m = S m} =
  let ih = lteExp {m} in
  transitive {po = LTE} 1 2 (2 ^ S m) (LTESucc LTEZero) (plusLteMonotone ih ih)

public export
toNat : {n : _} -> Path n -> Nat
toNat Here = Z
toNat (Left p) = toNat p
toNat {n = S n} (Right p) = toNat p + 2 ^ n

export
toNatBounded : (n : Nat) -> (p : Path n) -> toNat p `LT` 2 ^ n
toNatBounded Z Here = lteRefl
toNatBounded (S n) (Left p) =
    let prf = plusLteMonotoneRight (2 ^ n) 1 (2 ^ n) lteExp in
    transitive {spo = LT} (toNat p) (2 ^ n) (2 ^ S n) (toNatBounded n p) prf
toNatBounded (S n) (Right p) =
   plusLteMonotoneRight (2 ^ n) (S (toNat p)) (2 ^ n) (toNatBounded n p)

namespace FromNat

  ||| This pattern-matching in `fromNat` is annoying:
  ||| The    `Z (S _)` case is impossible
  ||| In the `k (S n)` case we want to branch on whether `k `LT` 2 ^ n`
  ||| and get our hands on some proofs.
  ||| This view factors out that work.
  public export
  data View : (k, n : Nat) -> Type where
    ZZ   : View Z Z
    SLT  : (0 p : k `LT` 2 ^ n) -> View k (S n)
    SNLT : (0 p : k `GTE` 2 ^ n) ->
           (0 rec : minus k (2 ^ n) `LT` 2 ^ n) -> View k (S n)

  public export
  view : (k, n : Nat) -> (0 _ : k `LT` (2 ^ n)) -> View k n
  view Z Z p = ZZ
  view (S _) Z p = void $ absurd (fromLteSucc p)
  view k (S n) p with (@@ lt k (2 ^ n))
    view k (S n) p | (True ** eq) = SLT (ltIsLT k (2 ^ n) eq)
    view k (S n) p | (False ** eq) = SNLT gte prf where

      0 gte : k `GTE` 2 ^ n
      gte = notLTImpliesGTE (notltIsNotLT k (2 ^ n) eq)

      0 bnd : minus k (2 ^ n) `LT` minus (2 ^ (S n)) (2 ^ n)
      bnd = minusLtMonotone p (plusLteMonotoneRight (2 ^ n) _ _ lteExp)

      0 prf : minus k (2 ^ n) `LT` 2 ^ n
      prf = replace {p = LTE _} (minusPlus _) bnd

||| Convert a natural number to a path in a perfect binary tree
public export
fromNat : (k, n : Nat) -> (0 _ : k `LT` (2 ^ n)) -> Path n
fromNat k n p with (view k n p)
  fromNat Z Z p | ZZ = Here
  fromNat k (S n) p | SLT lt = Left (fromNat k n lt)
  fromNat k (S n) p | SNLT _ lt = Right (fromNat (minus k (2 ^ n)) n lt)

||| The `fromNat` conversion is compatible with the semantics `toNat`
export
fromNatCorrect : (k, n : Nat) -> (0 p : k `LT` 2 ^ n) ->
                 toNat (fromNat k n p) === k
fromNatCorrect k n p with (view k n p)
  fromNatCorrect Z Z p | ZZ = Refl
  fromNatCorrect k (S n) p | SLT lt = fromNatCorrect k n lt
  fromNatCorrect k (S n) p | SNLT gte lt
     = rewrite fromNatCorrect (minus k (2 ^ n)) n lt in
       irrelevantEq $ plusMinusLte (2 ^ n) k gte

public export
lookup : Tree n a -> Path n -> a
lookup (Leaf a) Here = a
lookup (Node l _) (Left p) = lookup l p
lookup (Node _ r) (Right p) = lookup r p
