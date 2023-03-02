||| WellFounded on List suffixes
module Data.List.Sufficient

import Control.WellFounded

%default total

public export
data Suffix : (ys,xs : List a) -> Type where
  IsSuffix : (x : a) -> (zs : List a)
          -> (0 ford : xs = x :: zs ++ ys) -> Suffix ys xs

SuffixAccessible : (xs : List a) -> Accessible Suffix xs
SuffixAccessible [] = Access (\y => \case (IsSuffix x zs _) impossible)
SuffixAccessible ws@(x :: xs) =
  let fact1@(Access f) = SuffixAccessible xs
  in Access $ \ys => \case
    (IsSuffix x [] Refl) => fact1
    (IsSuffix x (z :: zs) Refl) => f ys (IsSuffix z zs Refl)

public export
WellFounded (List a) Suffix where
  wellFounded = SuffixAccessible
