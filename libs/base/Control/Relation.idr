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
