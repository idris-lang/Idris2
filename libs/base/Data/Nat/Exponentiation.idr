module Data.Nat.Exponentiation

import Data.Nat.Views

%default total

export
linear : Monoid a => a -> Nat -> a
linear m = go where

  go : Nat -> a
  go Z = neutral
  go (S k) = m <+> go k

export
modular : Monoid a => a -> Nat -> a
modular m k = go (halfRec k) where

  go : HalfRec n -> a
  go HalfRecZ = neutral
  go (HalfRecEven _ acc) = let e = go acc in e <+> e
  go (HalfRecOdd _ acc) = let e = go acc in m <+> e <+> e

-- TODO: proof the two definitions are equivalent for a monoid with laws

namespace Semigroup

  public export
  [ADDITIVE] Num a => Semigroup a
    where (<+>) = (+)
  public export
  [MULTIPLICATIVE] Num a => Semigroup a
    where (<+>) = (*)

namespace Monoid

  public export
  [ADDITIVE] Num a => Monoid a
    using Semigroup.ADDITIVE
    where neutral = 0
  public export
  [MULTIPLICATIVE] Num a => Monoid a
    using Semigroup.MULTIPLICATIVE
    where neutral = 1


infixl 10 ^
export
(^) : Num a => a -> Nat -> a
(^) = modular @{MULTIPLICATIVE}
