module Control.Ord

%default total

namespace Semigroup

  public export
  [Maximum] Ord a => Semigroup a where
    (<+>) = max

  public export
  [Minimum] Ord a => Semigroup a where
    (<+>) = min
