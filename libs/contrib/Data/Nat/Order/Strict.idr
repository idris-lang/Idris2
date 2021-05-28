||| Implementing `Decidable.Order.Strict` for `Data.Nat.LT`
module Data.Nat.Order.Strict

import Data.Nat
import Control.Relation
import Control.Order
import Decidable.Order.Strict
import Decidable.Equality
import Data.Nat.Order

%default total

public export
Irreflexive Nat LT where
  irreflexive {x = 0} _ impossible
  irreflexive {x = S k} (LTESucc prf) =
    -- why can't this be inlined?
    let rec = irreflexive {x = k} {rel = LT} in
      rec prf

public export
Transitive Nat LT where
  transitive {x} {y} xy yz =
    transitive {rel = LTE} (lteSuccRight xy) yz

public export
StrictPreorder Nat LT where

public export
decLT : (a, b : Nat) -> DecOrdering {lt = LT} a b
decLT 0       0   = DecEQ Refl
decLT 0     (S b) = DecLT (LTESucc LTEZero)
decLT (S a)  0    = DecGT (LTESucc LTEZero)
decLT (S a) (S b) = case decLT a b of
  DecLT a_lt_b => DecLT (LTESucc a_lt_b)
  DecEQ Refl   => DecEQ Refl
  DecGT b_lt_a => DecGT (LTESucc b_lt_a)

public export
StrictOrdered Nat LT where
  order = decLT
