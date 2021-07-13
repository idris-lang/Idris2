||| Implementation of ordering relations for `Nat`ural numbers
module Data.Nat.Order

import Control.Relation
import Data.Nat
import Data.Fun
import Data.Rel
import Decidable.Decidable
import Decidable.Equality

%default total

public export
zeroNeverGreater : {n : Nat} -> LTE (S n) Z -> Void
zeroNeverGreater LTEZero     impossible
zeroNeverGreater (LTESucc _) impossible

public export
zeroAlwaysSmaller : {n : Nat} -> LTE Z n
zeroAlwaysSmaller = LTEZero

public export
ltesuccinjective : {0 n, m : Nat} -> Not (LTE n m) -> Not (LTE (S n) (S m))
ltesuccinjective disprf (LTESucc nLTEm) = void (disprf nLTEm)
ltesuccinjective disprf LTEZero         impossible

public export
decideLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decideLTE    Z      y  = Yes LTEZero
decideLTE (S x)     Z  = No  zeroNeverGreater
decideLTE (S x)   (S y) with (decEq (S x) (S y))
  decideLTE (S x)   (S y) | Yes eq      = rewrite eq in Yes (reflexive {rel = LTE})
  decideLTE (S x)   (S y) | No _ with (decideLTE x y)
    decideLTE (S x)   (S y) | No _   | Yes nLTEm = Yes (LTESucc nLTEm)
    decideLTE (S x)   (S y) | No _   | No  nGTm  = No (ltesuccinjective nGTm)

public export
Decidable 2 [Nat,Nat] LTE where
  decide = decideLTE

public export
lte : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = LTE} m n

public export
shift : (m : Nat) -> (n : Nat) -> LTE m n -> LTE (S m) (S n)
shift m n mLTEn = LTESucc mLTEn
