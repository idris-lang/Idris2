||| Properties of binary relations
module Control.Relation

%default total

public export
interface Reflexive ty rel where
  reflexive : {x : ty} -> rel x x

public export
interface Transitive ty rel where
  transitive : {x, y, z : ty} -> rel x y -> rel y z -> rel x z

public export
interface Symmetric ty rel where
  symmetric : {x, y : ty} -> rel x y -> rel y x

public export
interface Antisymmetric ty rel where
  antisymmetric : {x, y : ty} -> rel x y -> rel y x -> x = y

public export
interface Dense ty rel where
  dense : {x, y : ty} -> rel x y -> (z : ty ** (rel x z, rel z y))

public export
interface Serial ty rel where
  serial : {x : ty} -> (y : ty ** rel x y)

public export
interface Euclidean ty rel where
  euclidean : {x, y, z : ty} -> rel x y -> rel x z -> rel y z

public export
interface (Reflexive ty rel, Symmetric ty rel) => Tolerance ty rel where

public export
interface (Transitive ty rel, Symmetric ty rel) => PartialEquivalence ty rel where

public export
interface (Reflexive ty rel, Transitive ty rel, Symmetric ty rel) => Equivalence ty rel where

----------------------------------------

public export
Reflexive ty rel => Dense ty rel where
  dense {x} xy = (x ** (reflexive {x}, xy))

public export
Reflexive ty rel => Serial ty rel where
  serial {x} = (x ** reflexive {x})

public export
(Transitive ty rel, Symmetric ty rel, Serial ty rel) => Reflexive ty rel where
  reflexive {x} =
    let (y ** xy) = serial {x} in
      transitive {x} xy $ symmetric {x} xy

public export
(Reflexive ty rel, Euclidean ty rel) => Symmetric ty rel where
  symmetric {x} xy = euclidean {x} xy $ reflexive {x}

public export
(Reflexive ty rel, Euclidean ty rel) => Transitive ty rel where
  transitive {rel} xy yz = symmetric {rel} $ euclidean {rel} yz $ symmetric {rel} xy

public export
(Transitive ty rel, Symmetric ty rel) => Euclidean ty rel where
  euclidean {rel} xy xz = transitive {rel} (symmetric {rel} xy) xz

----------------------------------------

public export
Reflexive ty Equal where
  reflexive = Refl

public export
Euclidean ty Equal where
  euclidean xy xz = trans (sym (xy)) xz

public export
Equivalence ty Equal where
