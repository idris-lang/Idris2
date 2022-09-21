||| Implementation of ordering relations for `Nat`ural numbers
module Data.Nat.Order

import Data.Nat
import Data.Fun
import Data.Rel
import Decidable.Decidable

%default total

public export
zeroNeverGreater : Not (LTE (S n) Z)
zeroNeverGreater LTEZero     impossible
zeroNeverGreater (LTESucc _) impossible

public export
zeroAlwaysSmaller : {n : Nat} -> LTE Z n
zeroAlwaysSmaller = LTEZero

public export
ltesuccinjective : {0 n, m : Nat} -> Not (LTE n m) -> Not (LTE (S n) (S m))
ltesuccinjective disprf (LTESucc nLTEm) = void (disprf nLTEm)
ltesuccinjective disprf LTEZero         impossible

-- Remove any time after release of 0.6.0
||| Deprecated. Use `Nat.isLTE`.
public export
decideLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decideLTE = isLTE

||| If a predicate is decidable then we can decide whether it holds on
||| a bounded domain.
public export
decideLTBounded :
  {0 p : Nat -> Type} ->
  ((n : Nat) -> Dec (p n)) ->
  (n : Nat) -> Dec ((k : Nat) -> k `LT` n -> p k)
decideLTBounded pdec 0 = Yes (\ k, bnd => absurd bnd)
decideLTBounded pdec (S n) with (pdec 0)
  _ | No np0 = No (\ prf => np0 (prf 0 (LTESucc LTEZero)))
  _ | Yes p0 with (decideLTBounded (\ n => pdec (S n)) n)
    _ | No nprf = No (\ prf => nprf (\ k, bnd => prf (S k) (LTESucc bnd)))
    _ | Yes prf = Yes $ \ k, bnd =>
      case view bnd of
        LTZero => p0
        (LTSucc bnd) => prf _ bnd

||| If a predicate is decidable then we can decide whether it holds on
||| a bounded domain.
public export
decideLTEBounded :
  {0 p : Nat -> Type} ->
  ((n : Nat) -> Dec (p n)) ->
  (n : Nat) -> Dec ((k : Nat) -> k `LTE` n -> p k)
decideLTEBounded pdec n with (decideLTBounded pdec (S n))
  _ | Yes prf = Yes (\ k, bnd => prf k (LTESucc bnd))
  _ | No nprf = No (\ prf => nprf (\ k, bnd => prf k (fromLteSucc bnd)))

public export
Decidable 2 [Nat,Nat] LTE where
  decide = decideLTE

public export
Decidable 2 [Nat,Nat] LT where
  decide m = decideLTE (S m)

public export
lte : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = LTE} m n

public export
shift : (m : Nat) -> (n : Nat) -> LTE m n -> LTE (S m) (S n)
shift m n mLTEn = LTESucc mLTEn
