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

%default total

-- The converse to lteIsLTE:
export
LteIslte : (a, b : Nat) -> a `LTE` b -> a `lte` b = True
                          -- DYI Syntax.PreorderReasoning from contrib
LteIslte  a b a_lt_b with (the (x : Bool ** a `lte` b = x) (a `lte` b ** Refl))
 LteIslte a b a_lt_b | (True  ** prf) = prf
 LteIslte a b a_lt_b | (False ** prf) = void $ irreflexive {spo = Data.Nat.LT} a 
   $ CalcWith {leq = LTE} $
   |~ 1 + a
   <~ 1 + b  ...(plusLteMonotoneLeft 1 a b a_lt_b)
   <~ a      ...(notlteIsLT _ _ prf)

-- The converse to lteIsLTE:
export
GTIsnotlte : (a, b : Nat) -> b `LT` a -> a `lte` b = False
                          -- DYI Syntax.PreorderReasoning from contrib
GTIsnotlte  a b b_lt_a with (the (x : Bool ** a `lte` b = x) (a `lte` b ** Refl))
 GTIsnotlte a b b_lt_a | (False ** prf) = prf
 GTIsnotlte a b b_lt_a | (True  ** prf) = void $ irreflexive {spo = Data.Nat.LT} b 
   $ CalcWith {leq = LTE} $
   |~ 1 + b
   <~ a  ...(b_lt_a)
   <~ b  ...(lteIsLTE _ _ prf)

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
