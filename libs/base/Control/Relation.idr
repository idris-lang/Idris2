||| Properties of binary relations
module Control.Relation

%default total

public export
interface Reflexive (ty : Type) (rel : ty -> ty -> Type) where
  reflexive : (x : ty) -> rel x x

public export
interface Transitive (ty : Type) (rel : ty -> ty -> Type) where
  transitive : (x, y, z : ty) -> rel x y -> rel y z -> rel x z

-- Equality implementations ------------

Reflexive ty Equal where
  reflexive _ = Refl

Transitive ty Equal where
  transitive _ _ _ xy yz = trans xy yz
