||| Properties of binary relations
module Control.Relation

%default total

public export
interface Reflexive ty rel where
  reflexive : (x : ty) -> rel x x

public export
interface Transitive ty rel where
  transitive : (x, y, z : ty) -> rel x y -> rel y z -> rel x z
