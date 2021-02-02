module Decidable.Finite.Fin

import Data.Nat
import Data.Nat.Order
import Data.Fin
import Decidable.Decidable.Extra
import Data.Fin.Extra

||| Given a decidable predicate on Fin n,
||| it's decidable whether any number in Fin n satisfies it.
public export
finiteDecEx : {n : Nat} -> {0 p : Fin n -> Type} ->
  (pdec : (k : Fin n) -> Dec (p k)) ->
  Dec (k ** p k)
finiteDecEx {n = Z} pdec = No (absurd . fst)
finiteDecEx {n = S n} pdec =
  case pdec FZ of
    Yes pz => Yes (FZ ** pz)
    No npz => case finiteDecEx {n = n} (\ k => pdec (FS k)) of
      Yes (k ** pk) => Yes (FS k ** pk)
      No npk => No $ \case
        (FZ ** pz) => absurd (npz pz)
        (FS k ** pk) => absurd (npk (k ** pk))



||| Given a decidable predicate on Fin n,
||| it's decidable whether all numbers in Fin n satisfy it.
public export
finiteDecAll : {n : Nat} -> {0 p : Fin n -> Type} ->
  (pdec : (k : Fin n) -> Dec (p k)) ->
  Dec ((k : Fin n) -> p k)
finiteDecAll pdec  = notExistsNotForall pdec $ finiteDecEx (\ x => negateDec (pdec x))
