||| A binary relation is a function of type (ty -> ty -> Type).
|||
||| A prominent example of a binary relation is LTE over Nat.
|||
||| This module defines some interfaces for describing properties of
||| binary relations. It also proves somes relations among relations.

module Control.Relation

%default total

||| A relation on ty is a type indexed by two ty values
public export
Rel : Type -> Type
Rel ty = ty -> ty -> Type

||| A relation is reflexive if x ~ x for every x.
public export
interface Reflexive ty rel | rel where
  constructor MkReflexive
  reflexive : {x : ty} -> rel x x

||| A relation is transitive if x ~ z when x ~ y and y ~ z.
public export
interface Transitive ty rel | rel where
  constructor MkTransitive
  transitive : {x, y, z : ty} -> rel x y -> rel y z -> rel x z

||| A relation is symmetric if y ~ x when x ~ y.
public export
interface Symmetric ty rel | rel where
  constructor MkSymmetric
  symmetric : {x, y : ty} -> rel x y -> rel y x

||| A relation is antisymmetric if no two distinct elements bear the relation to each other.
public export
interface Antisymmetric ty rel | rel where
  constructor MkAntisymmetric
  antisymmetric : {x, y : ty} -> rel x y -> rel y x -> x = y

||| A relation is dense if when x ~ y there is z such that x ~ z and z ~ y.
public export
interface Dense ty rel | rel where
  constructor MkDense
  dense : {x, y : ty} -> rel x y -> (z : ty ** (rel x z, rel z y))

||| A relation is serial if for all x there is a y such that x ~ y.
public export
interface Serial ty rel | rel where
  constructor MkSerial
  serial : {x : ty} -> (y : ty ** rel x y)

||| A relation is euclidean if y ~ z when x ~ y and x ~ z.
public export
interface Euclidean ty rel | rel where
  constructor MkEuclidean
  euclidean : {x, y, z : ty} -> rel x y -> rel x z -> rel y z

||| A tolerance relation is reflexive and symmetric.
public export
interface (Reflexive ty rel, Symmetric ty rel) => Tolerance ty rel | rel where

||| A partial equivalence is transitive and symmetric.
public export
interface (Transitive ty rel, Symmetric ty rel) => PartialEquivalence ty rel | rel where

||| An equivalence relation is transitive, symmetric, and reflexive.
public export
interface (Reflexive ty rel, Transitive ty rel, Symmetric ty rel) => Equivalence ty rel | rel where

----------------------------------------

||| Every reflexive relation is dense.
public export
Reflexive ty rel => Dense ty rel where
  dense xy = (x ** (reflexive, xy))

||| Every reflexive relation is serial.
public export
Reflexive ty rel => Serial ty rel where
  serial = (x ** reflexive)

||| A transitive symmetric serial relation is reflexive.
public export
(Transitive ty rel, Symmetric ty rel, Serial ty rel) => Reflexive ty rel where
  reflexive = let (y ** xy) = serial in transitive xy $ symmetric xy

||| A reflexive euclidean relation is symmetric.
public export
[RES] (Reflexive ty rel, Euclidean ty rel) => Symmetric ty rel where
  symmetric xy = euclidean xy $ reflexive

||| A reflexive euclidean relation is transitive.
public export
[RET] (Reflexive ty rel, Euclidean ty rel) =>
      Transitive ty rel using RES where
  transitive xy yz = symmetric $ euclidean yz $ symmetric xy

||| A transitive symmetrics relation is euclidean.
public export
[TSE] (Transitive ty rel, Symmetric ty rel) => Euclidean ty rel where
  euclidean xy xz = transitive (symmetric xy) xz

----------------------------------------

public export
Reflexive ty Equal where
  reflexive = Refl

public export
Symmetric ty Equal where
  symmetric xy = sym xy

public export
Transitive ty Equal where
  transitive xy yz = trans xy yz

public export
Euclidean ty Equal where
  euclidean = euclidean @{TSE}

public export
Tolerance ty Equal where

public export
PartialEquivalence ty Equal where

public export
Equivalence ty Equal where
