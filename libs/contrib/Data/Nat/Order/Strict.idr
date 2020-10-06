||| Implementing `Decidable.Order.Strict` for `Data.Nat.LT`
module Data.Nat.Order.Strict

import Decidable.Order
import Decidable.Order.Strict
import Decidable.Equality
import Data.Nat
import Data.Nat.Order

export
irreflexiveLTE : (a : Nat) -> Not (a `LT` a)
irreflexiveLTE 0     z_lt_z impossible
irreflexiveLTE (S a) (LTESucc a_lt_a) = irreflexiveLTE a a_lt_a

export
StrictPreorder Nat LT where
  irreflexive = irreflexiveLTE
  transitive a b c a_lt_b b_lt_c = transitive {po = LTE} (S a) b c
                                             a_lt_b
                                             (transitive {po = LTE} b (S b) c
                                                (lteSuccRight (reflexive b))
                                                b_lt_c)

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
