module Data.Linear.LEither

import Data.Linear.Bifunctor
import Data.Linear.Interface
import Data.Linear.Notation

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
(Duplicable a, Duplicable b) => Duplicable (LEither a b) where
  duplicate (Left a) = Left <$> duplicate a
  duplicate (Right b) = Right <$> duplicate b
