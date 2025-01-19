module Implementation

import Data.String

data OneTwoThree a
  = One a
  | Two a a
  | Three a a a

[OTT] Functor OneTwoThree where
  map f = \case
    One x => One (f x)
    Two x y => Two (f x) (f y)
    Three x y z => Three (f x) (f y) (f z)

Show a => Show (OneTwoThree a) where
  show (One x) = "One " ++ show x
  show (Two x y) = unwords ["Two", show x, show y]
  show (Three x y z) = unwords ["Three", show x, show y, show z]

Eq a => Eq (OneTwoThree a) where
  One a == One x = a == x
  Two a b == Two x y = a == x && b == y
  Three a b c == Three x y z = a == x && b == y && c == z
  _ == _ = False
