module Data.Morphisms.Algebra

import Control.Algebra
import Data.Morphisms

%default total

public export
SemigroupV (Endomorphism ty) where
  semigroupOpIsAssociative (Endo _) (Endo _) (Endo _) = Refl

public export
MonoidV (Endomorphism ty) where
  monoidNeutralIsNeutralL (Endo _) = Refl
  monoidNeutralIsNeutralR (Endo _) = Refl
