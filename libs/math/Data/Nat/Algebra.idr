module Data.Nat.Algebra

import Control.Algebra
import Data.Nat

%default total

namespace SemigroupV

  public export
  [Additive] SemigroupV Nat using Semigroup.Additive where
    semigroupOpIsAssociative = plusAssociative

namespace MonoidV

  public export
  [Additive] MonoidV Nat using Monoid.Additive SemigroupV.Additive where
    monoidNeutralIsNeutralL = plusZeroRightNeutral
    monoidNeutralIsNeutralR = plusZeroLeftNeutral
