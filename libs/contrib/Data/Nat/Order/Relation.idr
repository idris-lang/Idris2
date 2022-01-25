||| An example implementation for the Tolerance relation.

module Data.Nat.Order.Relation

import Control.Relation

Adjacent : (a, b : Nat) -> Type
Adjacent a b = Either (a = b) $ Either (a = S b) (b = S a)

Reflexive Nat Adjacent where
  reflexive = Left Refl

Symmetric Nat Adjacent where
  symmetric (Left x_eq_y) = Left $ sym x_eq_y
  symmetric (Right $  Left prf) = Right $ Right prf
  symmetric (Right $ Right prf) = Right $  Left prf

Tolerance Nat Adjacent where
