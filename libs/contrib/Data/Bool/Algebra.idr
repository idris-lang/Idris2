module Data.Bool.Algebra

import Control.Algebra
import Data.Bool.Xor

%default total

-- && is Bool -> Lazy Bool -> Bool,
-- but Bool -> Bool -> Bool is required
and : Bool -> Bool -> Bool
and True True = True
and _ _ = False

Semigroup Bool where
  (<+>) = xor

SemigroupV Bool where
  semigroupOpIsAssociative = xorAssociative

Monoid Bool where
  neutral = False

MonoidV Bool where
  monoidNeutralIsNeutralL True = Refl
  monoidNeutralIsNeutralL False = Refl

  monoidNeutralIsNeutralR True = Refl
  monoidNeutralIsNeutralR False = Refl

Group Bool where
  -- Each Bool is its own additive inverse.
  inverse = id

  groupInverseIsInverseR True = Refl
  groupInverseIsInverseR False = Refl

AbelianGroup Bool where
  groupOpIsCommutative = xorCommutative

Ring Bool where
  (<.>) = and

  ringOpIsAssociative True True True = Refl
  ringOpIsAssociative True True False = Refl
  ringOpIsAssociative True False True = Refl
  ringOpIsAssociative True False False = Refl
  ringOpIsAssociative False True True = Refl
  ringOpIsAssociative False False True = Refl
  ringOpIsAssociative False True False = Refl
  ringOpIsAssociative False False False = Refl

  ringOpIsDistributiveL True True True = Refl
  ringOpIsDistributiveL True True False = Refl
  ringOpIsDistributiveL True False True = Refl
  ringOpIsDistributiveL True False False = Refl
  ringOpIsDistributiveL False True True = Refl
  ringOpIsDistributiveL False False True = Refl
  ringOpIsDistributiveL False True False = Refl
  ringOpIsDistributiveL False False False = Refl

  ringOpIsDistributiveR True True True = Refl
  ringOpIsDistributiveR True True False = Refl
  ringOpIsDistributiveR True False True = Refl
  ringOpIsDistributiveR True False False = Refl
  ringOpIsDistributiveR False True True = Refl
  ringOpIsDistributiveR False False True = Refl
  ringOpIsDistributiveR False True False = Refl
  ringOpIsDistributiveR False False False = Refl

RingWithUnity Bool where
  unity = True

  unityIsRingIdL True = Refl
  unityIsRingIdL False = Refl

  unityIsRingIdR True = Refl
  unityIsRingIdR False = Refl
