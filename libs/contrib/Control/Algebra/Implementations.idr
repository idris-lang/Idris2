module Control.Algebra.Implementations

import Control.Algebra

-- This file is for algebra implementations with nowhere else to go.

%default total

-- Functions ---------------------------

Semigroup (ty -> ty) where
  (<+>) = (.)

SemigroupV (ty -> ty) where
  semigroupOpIsAssociative _ _ _ = Refl

Monoid (ty -> ty) where
  neutral = id

MonoidV (ty -> ty) where
  monoidNeutralIsNeutralL _ = Refl
  monoidNeutralIsNeutralR _ = Refl
