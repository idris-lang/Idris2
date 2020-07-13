module Data.List.Algebra

import Control.Algebra
import Data.List

%default total

public export
SemigroupV (List ty) where
  semigroupOpIsAssociative = appendAssociative

public export
MonoidV (List ty) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR _ = Refl
