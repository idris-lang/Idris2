module Decidable.Decidable

import Data.Rel
import Data.Fun

%default total

public export
isNo : Dec a -> Bool
isNo (Yes _) = False
isNo (No _) = True

public export
isYes : Dec a -> Bool
isYes (Yes _) = True
isYes (No _) = False

export
Injective Yes where
  injective Refl = Refl

export
Injective No where
  injective Refl = Refl

||| Proof that some `Dec` is actually `Yes`
public export
data IsYes : Dec a -> Type where
  ItIsYes : IsYes (Yes prf)

public export
Uninhabited (IsYes (No contra)) where
  uninhabited ItIsYes impossible

||| Decide whether a 'Dec' is 'Yes'
public export
isItYes : (v : Dec a) -> Dec (IsYes v)
isItYes (Yes _) = Yes ItIsYes
isItYes (No _) = No absurd

||| An n-ary relation is decidable if we can make a `Dec`
||| of its result type for each combination of inputs
public export
IsDecidable : (k : Nat) -> (ts : Vect k Type) -> Rel ts -> Type
IsDecidable k ts p = liftRel ts p Dec

||| Interface for decidable n-ary Relations
public export
interface Decidable k ts p where
  total decide : IsDecidable k ts p

||| Given a `Decidable` n-ary relation, provides a decision procedure for
||| this relation.
decision : (ts : Vect k Type) -> (p : Rel ts) -> Decidable k ts p => liftRel ts p Dec
decision ts p = decide {ts} {p}
