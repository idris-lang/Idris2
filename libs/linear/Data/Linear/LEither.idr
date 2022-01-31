module Data.Linear.LEither

import Data.Linear.Notation
import Data.Linear.Bifunctor

%default total

public export
data LEither : (a, b : Type) -> Type where
  Left : a -@ LEither a b
  Right : b -@ LEither a b

export
(Consumable a, Consumable b) => Consumable (LEither a b) where
  consume (Left a) = consume a
  consume (Right b) = consume b

export
(Duplicate a, Duplicate b) => Duplicate (LEither a b) where
  dup (Left a) = bimap Left Left (Notation.dup a)
  dup (Right b) = bimap Right Right (Notation.dup b)
