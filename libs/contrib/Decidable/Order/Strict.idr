||| An strict preorder (sometimes known as a quasi-order, or an
||| ordering) is what you get when you remove the diagonal `{(a,b) | a
||| r b , b r a}` from a preorder. For example a < b is an ordering.
||| This module extends base's Decidable.Order with the strict versions.
||| The interface system seems to struggle a bit with some of the constructions,
||| so I hacked them a bit. Sorry.
module Decidable.Order.Strict

import Decidable.Order
import Decidable.Equality

%default total

public export
interface StrictComparison t where
  scmp : t -> t -> Type

public export
interface StrictComparison t => StrictPreorder t where
  transitive : (a, b, c : t) -> a `scmp` b -> b `scmp` c -> a `scmp` c
  irreflexive : (a : t) -> Not (a `scmp` a)

public export
asymmetric : StrictPreorder t => (a, b : t) -> a `scmp` b -> Not (b `scmp` a)
asymmetric a b aLTb bLTa = irreflexive a $ 
                           Strict.transitive a b a aLTb bLTa

public export
EqOr : (spo : t -> t -> Type) -> (a,b : t) -> Type
EqOr spo a b = Either (a = b) (a `spo` b)

public export
[EqOrCmp] (StrictComparison t) => ComparisonRelation t where
  cmp = EqOr scmp

-- Can generalise to an arbitrary equivalence, I belive
public export
[EqOrPreorder] StrictPreorder t => Preorder t using EqOrCmp where
  reflexive a = Left Refl
  transitive a _ c (Left  Refl) bLTEc        = bLTEc
  transitive a b _ (Right aLTb) (Left  Refl) = Right aLTb
  transitive a b c (Right aLTb) (Right bLTc) = Right $ Strict.transitive a b c aLTb bLTc

[EqOrPoset] StrictPreorder t => Poset t using EqOrPreorder where
  antisymmetric a a (Left  Refl) (Left  Refl) = Refl
  antisymmetric a a (Left  Refl) (Right bLTa) = absurd (irreflexive a bLTa)
  antisymmetric b b (Right aLTb) (Left  Refl) = absurd (irreflexive b aLTb)
  antisymmetric a b (Right aLTb) (Right bLTa) = absurd (asymmetric a b aLTb bLTa)

public export
data DecOrdering : {lt : t -> t -> Type} -> (a,b : t) -> Type where
  DecLT : forall lt . (a `lt` b) -> DecOrdering {lt = lt} a b
  DecEQ : forall lt . (a  =   b) -> DecOrdering {lt = lt} a b
  DecGT : forall lt . (b `lt` a) -> DecOrdering {lt = lt} a b 

public export
interface (StrictPreorder t) => StrictOrdered t where
  order : (a,b : t) -> DecOrdering {lt = Strict.scmp} a b

public export
implementation StrictOrdered t => Ordered t using EqOrPoset where
  order  a b with (Strict.order a b)
   order a _ | DecEQ Refl = Left  (Left  Refl)
   order a b | DecLT aLTb = Left  (Right aLTb)
   order a b | DecGT bLTa = Right (Right bLTa)


public export
implementation (tot : StrictOrdered t) => DecEq t where
  decEq x y = case order x y of
    DecEQ x_eq_y => Yes x_eq_y
    DecLT xlty => No $ \x_eq_y => absurd $ irreflexive y 
                                         $ replace {p = \u => u `scmp` y} x_eq_y xlty
    -- Similarly                                         
    DecGT yltx => No $ \x_eq_y => absurd $ irreflexive y
                                         $ replace {p = \u => y `scmp` u} x_eq_y yltx
    
