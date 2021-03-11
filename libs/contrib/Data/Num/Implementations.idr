module Data.Num.Implementations

%default total

namespace Semigroup

  public export
  [Additive] Num a => Semigroup a
    where (<+>) = (+)
  public export
  [Multiplicative] Num a => Semigroup a
    where (<+>) = (*)

namespace Monoid

  public export
  [Additive] Num a => Monoid a
    using Semigroup.Additive
    where neutral = 0
  public export
  [Multiplicative] Num a => Monoid a
    using Semigroup.Multiplicative
    where neutral = 1
