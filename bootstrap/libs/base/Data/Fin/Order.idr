||| Implementation  of ordering relations for `Fin`ite numbers
module Data.Fin.Order

import Data.Fin
import Data.Fun
import Data.Rel
import Data.Nat
import Data.Nat.Order
import Decidable.Decidable
import Decidable.Order

using (k : Nat)

  public export
  data FinLTE : Fin k -> Fin k -> Type where
    FromNatPrf : {m, n : Fin k} -> LTE (finToNat m) (finToNat n) -> FinLTE m n

  public export
  implementation Preorder (Fin k) FinLTE where
    transitive m n o (FromNatPrf p1) (FromNatPrf p2) =
      FromNatPrf (LTEIsTransitive (finToNat m) (finToNat n) (finToNat o) p1 p2)
    reflexive n = FromNatPrf (LTEIsReflexive (finToNat n))

  public export
  implementation Poset (Fin k) FinLTE where
    antisymmetric m n (FromNatPrf p1) (FromNatPrf p2) =
      finToNatInjective m n (LTEIsAntisymmetric (finToNat m) (finToNat n) p1 p2)

  public export
  implementation Decidable 2 [Fin k, Fin k] FinLTE where
    decide m n with (decideLTE (finToNat m) (finToNat n))
      decide m n | Yes prf    = Yes (FromNatPrf prf)
      decide m n | No  disprf = No (\ (FromNatPrf prf) => disprf prf)

  public export
  implementation Ordered (Fin k) FinLTE where
    order m n =
      either (Left . FromNatPrf)
             (Right . FromNatPrf)
             (order (finToNat m) (finToNat n))
