||| Additional properties/lemmata of Nats involving order
module Data.Nat.Order.Properties

import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Strict
import Decidable.Equality
import Decidable.Order
import Decidable.Order.Strict
import Data.Bool.Decidable


%default total
export
LTESuccInjectiveMonotone : (m, n : Nat) -> Reflects (m `LTE` n) b -> Reflects (S m `LTE` S n) b
LTESuccInjectiveMonotone m n (RTrue      m_lte_n) = RTrue  $ LTESucc m_lte_n
LTESuccInjectiveMonotone m n (RFalse not_m_lte_n) = RFalse $ \case
                                                               LTESucc m_lte_n => not_m_lte_n m_lte_n

export
lteReflection : (a, b : Nat) -> Reflects (a `LTE` b) (a `lte` b)
lteReflection 0 b = RTrue LTEZero
lteReflection (S k) 0 = RFalse \sk_lte_z => absurd sk_lte_z
lteReflection (S a) (S b) = LTESuccInjectiveMonotone a b (lteReflection a b)

-- For example:
export
lteIsLTE : (a, b : Nat) -> a `lte` b = True -> a `LTE` b
lteIsLTE  a b prf = invert (replace {p = Reflects (a `LTE` b)} prf (lteReflection a b))

export
notlteIsLT : (a, b : Nat) -> a `lte` b = False -> b `LT` a
notlteIsLT a b prf = notLTImpliesGTE
                       \prf' =>
                         (invert $ replace {p = Reflects (S a `LTE` S b)} prf
                                 $ lteReflection (S a) (S b)) prf'


-- The converse to lteIsLTE:
export
LteIslte : (a, b : Nat) -> a `LTE` b -> a `lte` b = True
LteIslte  a b a_lt_b = reflect (lteReflection a b) a_lt_b

-- The converse to lteIsLTE with negation
export
notLteIsnotlte : (a, b : Nat) -> Not (a `LTE` b) -> a `lte` b = False
notLteIsnotlte a b not_a_lte_b = reflect (lteReflection a b) not_a_lte_b

-- The converse to lteIsLTE:
export
GTIsnotlte : (a, b : Nat) -> b `LT` a -> a `lte` b = False
GTIsnotlte a b b_lt_a =
  let not_a_lte_b : Not (a `LTE` b)
      not_a_lte_b = \a_lte_b => irreflexive {spo = Nat.LT} a $ CalcWith {leq = LTE} $
        |~ 1 + a
        <~ 1 + b ...(plusLteMonotoneLeft 1 a b a_lte_b)
        <~ a     ...(b_lt_a)
  in notLteIsnotlte a b not_a_lte_b

||| Subtracting a number gives a smaller number
export
minusLTE : (a,b : Nat) -> (b `minus` a) `LTE` b
minusLTE a      0    = LTEZero
minusLTE 0     (S b) = reflexive (S b)
minusLTE (S a) (S b) = transitive (minus b a) b (S b)
                         (minusLTE a b)
                         (lteSuccRight (reflexive b))

||| Subtracting a positive number gives a strictly smaller number
export
minusPosLT : (a,b : Nat) -> 0 `LT` a -> a `LTE` b -> (b `minus` a) `LT` b
minusPosLT 0     b     z_lt_z           a_lte_b impossible
minusPosLT (S a) 0     z_lt_sa          a_lte_b impossible
minusPosLT (S a) (S b) z_lt_sa          a_lte_b = LTESucc (minusLTE a b)

-- This is the opposite of the convention in `Data.Nat`, but 'monotone on the left' means the below
export
multLteMonotoneRight : (l, a, b : Nat) -> a `LTE` b -> l*a `LTE` l*b
multLteMonotoneRight  0    a b _ = LTEZero
multLteMonotoneRight (S k) a b a_lte_b = CalcWith {leq = LTE} $
  |~ (1 + k) * a
  ~~ a +  k*a    ...(Refl)
  <~ b +  k*a    ...(plusLteMonotoneRight (k*a) a b a_lte_b)
  <~ b +  k*b    ...(plusLteMonotoneLeft  b (k*a) (k*b) $
                     multLteMonotoneRight k    a     b   a_lte_b)
  ~~ (1 + k) * b ...(Refl)

export
multLteMonotoneLeft : (a, b, r : Nat) -> a `LTE` b -> a*r `LTE` b*r
multLteMonotoneLeft a b r a_lt_b =
  rewrite multCommutative a r in
  rewrite multCommutative b r in
  multLteMonotoneRight r a b a_lt_b
