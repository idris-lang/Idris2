module Data.Rel.Complement

import Data.Rel
import Data.Fun
import Data.Fun.Extra
import Data.HVect

%default total

||| The logical complement of a relation.
public export
complement : {ts : Vect n Type} -> (p : Rel ts) -> Rel ts
complement = chain Not


||| The negation of a relation for some elements
||| is equal to the complement of the relation.
public export
notToComplement :
  {0 ts : Vect n Type}
  -> (p : Rel ts)
  -> (elems : HVect ts)
  -> Not (uncurry p elems) = uncurry (complement {ts = ts} p) elems
notToComplement p  = chainUncurry p Not
