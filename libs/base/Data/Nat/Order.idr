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
