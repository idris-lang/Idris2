module Control.Relation.Closure

import Control.Relation

%default total

public export
data SymClosure : Rel ty -> ty -> ty -> Type where
  Fwd : {0 x, y : ty} -> rel x y -> SymClosure rel x y
  Bwd : {0 x, y : ty} -> rel y x -> SymClosure rel x y

public export
Reflexive ty rel => Reflexive ty (SymClosure rel) where
  reflexive = Fwd reflexive

public export
Symmetric ty (SymClosure rel) where
  symmetric (Fwd xy) = Bwd xy
  symmetric (Bwd yx) = Fwd yx

----------------------------------------

public export
data TransClosure : Rel ty -> ty -> ty -> Type where
  Nil  : TransClosure rel x x
  (::) : {y : ty} -> rel x y -> TransClosure rel y z -> TransClosure rel x z

public export
Reflexive ty (TransClosure rel) where
  reflexive = []

public export
Symmetric ty rel => Symmetric ty (TransClosure rel) where
  symmetric {x} {y} xy = reverseOnto [] xy
    where
      reverseOnto : {z : ty} ->
                    TransClosure rel z x ->
                    TransClosure rel z y ->
                    TransClosure rel y x
      reverseOnto zx [] = zx
      reverseOnto zx (zw :: wy) = reverseOnto (symmetric zw :: zx) wy

public export
Transitive ty (TransClosure rel) where
  transitive [] yz = yz
  transitive (xw :: wy) yz = xw :: transitive wy yz

public export
Symmetric ty rel => Euclidean ty (TransClosure rel) where
  euclidean = euclidean @{TSE}

public export
Symmetric ty rel => Tolerance ty (TransClosure rel) where

public export
Symmetric ty rel => PartialEquivalence ty (TransClosure rel) where

public export
Symmetric ty rel => Equivalence ty (TransClosure rel) where
