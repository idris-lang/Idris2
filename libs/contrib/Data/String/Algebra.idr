module Data.String.Algebra

import Control.Algebra
import Data.String

%default total

export
SemigroupV String where
  semigroupOpIsAssociative = strAppendAssociative

export
MonoidV String where
  monoidNeutralIsNeutralL = strAppendEmptyRightNeutral
  monoidNeutralIsNeutralR = strAppendEmptyLeftNeutral
