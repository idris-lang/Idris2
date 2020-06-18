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

----------------------------------------

Reflexive ty rel => Dense ty rel where
  dense {x} xy = (x ** (reflexive {x}, xy))

Reflexive ty rel => Serial ty rel where
  serial {x} = (x ** reflexive {x})

(Transitive ty rel, Symmetric ty rel, Serial ty rel) => Reflexive ty rel where
  reflexive {x} =
    let (y ** xy) = serial {x} in
      transitive {x} xy $ symmetric {x} xy
