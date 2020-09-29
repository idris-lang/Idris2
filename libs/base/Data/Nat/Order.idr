||| Implementation of ordering relations for `Nat`ural numbers
module Data.Nat.Order

import Data.Nat
import Data.Fun
import Data.Rel
import Decidable.Decidable
import Decidable.Equality
import Decidable.Order

public export
total LTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           LTE m n -> LTE n o ->
                           LTE m o
LTEIsTransitive Z n o                 LTEZero                  nlteo   = LTEZero
LTEIsTransitive (S m) (S n) (S o) (LTESucc mlten)    (LTESucc nlteo)   = LTESucc (LTEIsTransitive m n o mlten nlteo)

public export
total LTEIsReflexive : (n : Nat) -> LTE n n
LTEIsReflexive Z      = LTEZero
LTEIsReflexive (S n)  = LTESucc (LTEIsReflexive n)

public export
implementation Preorder Nat LTE where
  transitive = LTEIsTransitive
  reflexive  = LTEIsReflexive

public export
total LTEIsAntisymmetric : (m : Nat) -> (n : Nat) ->
                              LTE m n -> LTE n m -> m = n
LTEIsAntisymmetric Z Z         LTEZero LTEZero = Refl
LTEIsAntisymmetric (S n) (S m) (LTESucc mLTEn) (LTESucc nLTEm) with (LTEIsAntisymmetric n m mLTEn nLTEm)
   LTEIsAntisymmetric (S n) (S n) (LTESucc mLTEn) (LTESucc nLTEm)    | Refl = Refl


public export
implementation Poset Nat LTE where
  antisymmetric = LTEIsAntisymmetric

public export
total zeroNeverGreater : {n : Nat} -> LTE (S n) Z -> Void
zeroNeverGreater {n} LTEZero     impossible
zeroNeverGreater {n} (LTESucc _) impossible

public export
total zeroAlwaysSmaller : {n : Nat} -> LTE Z n
zeroAlwaysSmaller = LTEZero

public export
total ltesuccinjective : {0 n : Nat} -> {0 m : Nat} -> (LTE n m -> Void) -> LTE (S n) (S m) -> Void
ltesuccinjective {n} {m} disprf (LTESucc nLTEm) = void (disprf nLTEm)
ltesuccinjective {n} {m} disprf LTEZero         impossible

public export
total decideLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decideLTE    Z      y  = Yes LTEZero
decideLTE (S x)     Z  = No  zeroNeverGreater
decideLTE (S x)   (S y) with (decEq (S x) (S y))
  decideLTE (S x)   (S y) | Yes eq      = rewrite eq in Yes (reflexive (S y))
  decideLTE (S x)   (S y) | No _ with (decideLTE x y)
  decideLTE (S x)   (S y) | No _   | Yes nLTEm = Yes (LTESucc nLTEm)
  decideLTE (S x)   (S y) | No _   | No  nGTm  = No (ltesuccinjective nGTm)

public export
implementation Decidable [Nat,Nat] LTE where
  decide = decideLTE

public export
total
lte : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = LTE} m n

public export
total
shift : (m : Nat) -> (n : Nat) -> LTE m n -> LTE (S m) (S n)
shift m n mLTEn = LTESucc mLTEn

public export
implementation Ordered Nat LTE where
  order Z      n = Left LTEZero
  order m      Z = Right LTEZero
  order (S k) (S j) with (order {to=LTE} k j)
    order (S k) (S j) | Left  prf = Left  (shift k j prf)
    order (S k) (S j) | Right prf = Right (shift j k prf)
