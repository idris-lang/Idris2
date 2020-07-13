module Data.Nat.Algebra

import Control.Algebra
import Data.Nat

%default total

public export
SemigroupV Nat where
  semigroupOpIsAssociative = plusAssociative

public export
MonoidV Nat where
  monoidNeutralIsNeutralL = plusZeroRightNeutral
  monoidNeutralIsNeutralR = plusZeroLeftNeutral
