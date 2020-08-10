module Control.Monad.Algebra

import Control.Algebra
import Control.Monad.Identity

%default total

public export
SemigroupV ty => SemigroupV (Identity ty) where
  semigroupOpIsAssociative (Id l) (Id c) (Id r) =
    rewrite semigroupOpIsAssociative l c r in Refl

public export
MonoidV ty => MonoidV (Identity ty) where
  monoidNeutralIsNeutralL (Id l) =
    rewrite monoidNeutralIsNeutralL l in Refl
  monoidNeutralIsNeutralR (Id r) =
    rewrite monoidNeutralIsNeutralR r in Refl
