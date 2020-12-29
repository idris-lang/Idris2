module Decidable.Decidable

import Data.Rel
import Data.Fun

||| An n-ary relation is decidable if we can make a `Dec`
||| of its result type for each combination of inputs
public export
IsDecidable : (k : Nat) -> (ts : Vect k Type) -> Rel ts -> Type
IsDecidable k ts p = liftRel (the (Vect k Type) ts) (the (Rel ts) p) Dec

||| Interface for decidable n-ary Relations
public export
interface Decidable k ts p where
  total decide : IsDecidable k ts p

||| Given a `Decidable` n-ary relation, provides a decision procedure for
||| this relation.
decision : (ts : Vect k Type) -> (p : Rel ts) -> (Decidable k ts p) => liftRel ts p Dec
decision ts p = decide {ts} {p}

using (a : Type, x : a)
  public export
  data Given : Dec a -> Type where
    Always : Given (Yes x)
