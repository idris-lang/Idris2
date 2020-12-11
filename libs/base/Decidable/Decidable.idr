module Decidable.Decidable

import Data.Rel
import Data.Fun

||| Interface for decidable n-ary Relations
public export
interface Decidable k ts p where
  total decide : liftRel (the (Vect k Type) ts) (the (Rel ts) p) Dec

||| Given a `Decidable` n-ary relation, provides a decision procedure for
||| this relation.
decision : (ts : Vect k Type) -> (p : Rel ts) -> (Decidable k ts p) => liftRel ts p Dec
decision ts p = decide {ts} {p}

using (a : Type, x : a)
  public export
  data Given : Dec a -> Type where
    Always : Given (Yes x)
