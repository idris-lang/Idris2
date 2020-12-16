module Data.Rel.Extra

import Data.Rel
import Data.Fun
import Data.Fun.Extra
import Data.HVect

%default total

||| The logical complement of a relation.
public export
complement : {ts : Vect n Type} -> (p : Rel ts) -> Rel ts
complement {ts = []} p = Not p
complement {ts = t :: ts} p = \x => complement (p x)

||| The negation of a relation for some elements
||| implies that they are in the complement of the relation.
public export
notToComplement :
  {0 ts : Vect n Type}
  -> (p : Rel ts)
  -> (elems : HVect ts)
  -> Not (uncurry p elems)
  -> uncurry (complement {ts = ts} p) elems
notToComplement p [] npf = npf
notToComplement p (x :: xs) npf = notToComplement (p x) xs npf

||| Elements being in the complement of a relation
||| imply that they are not in the relation.
public export
complementToNot : {0 ts : Vect n Type}
  -> (p : Rel ts)
  -> (elems : HVect ts)
  -> uncurry (complement {ts = ts} p) elems
  -> Not (uncurry p elems)
complementToNot p [] compPf = compPf
complementToNot p (x :: xs) compPf = complementToNot (p x) xs compPf
