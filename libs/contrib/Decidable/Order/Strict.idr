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
interface StrictPreorder t (spo : t -> t -> Type) where
  transitive : (a, b, c : t) -> a `spo` b -> b `spo` c -> a `spo` c
  irreflexive : (a : t) -> Not (a `spo` a)
  
public export
asymmetric : StrictPreorder t spo => (a, b : t) -> a `spo` b -> Not (b `spo` a)
asymmetric a b aLTb bLTa = irreflexive a $ 
                           Strict.transitive a b a aLTb bLTa

public export
EqOr : (spo : t -> t -> Type) -> StrictPreorder t spo => (a,b : t) -> Type
EqOr spo a b = Either (a = b) (a `spo` b)

-- Can generalise to an arbitrary equivalence, I belive
public export
[MkPreorder] {spo : t -> t -> Type} -> StrictPreorder t spo => Preorder t (EqOr spo) where
  reflexive a = Left Refl
  transitive a _ c (Left  Refl) bLTEc        = bLTEc
  transitive a b _ (Right aLTb) (Left  Refl) = Right aLTb
  transitive a b c (Right aLTb) (Right bLTc) = Right $ Strict.transitive a b c aLTb bLTc

[MkPoset] {antisym : (a,b : t) -> a `leq` b -> b `leq` a -> a = b} -> Preorder t leq => Poset t leq where
  antisymmetric = antisym
           
%hint
public export
InferPoset : {t : Type} -> {spo : t -> t -> Type} -> StrictPreorder t spo => Poset t (EqOr spo) 
InferPoset {t} {spo} = MkPoset @{MkPreorder} {antisym = antisym}
  where
    antisym : (a,b : t) -> EqOr spo a b -> EqOr spo b a -> a = b
    antisym a a (Left  Refl) (Left  Refl) = Refl
    antisym a a (Left  Refl) (Right bLTa) = absurd (irreflexive a bLTa)
    antisym b b (Right aLTb) (Left  Refl) = absurd (irreflexive b aLTb)
    antisym a b (Right aLTb) (Right bLTa) = absurd (asymmetric a b aLTb bLTa)

public export
data DecOrdering : {lt : t -> t -> Type} -> (a,b : t) -> Type where
  DecLT : forall lt . (a `lt` b) -> DecOrdering {lt = lt} a b
  DecEQ : forall lt . (a  =   b) -> DecOrdering {lt = lt} a b
  DecGT : forall lt . (b `lt` a) -> DecOrdering {lt = lt} a b 

public export
interface StrictPreorder t spo => StrictOrdered t (spo : t -> t -> Type) where
  order : (a,b : t) -> DecOrdering {lt = spo} a b 

[MkOrdered] {ord : (a,b : t) -> Either (a `leq` b) (b `leq` a)} -> Poset t leq => Ordered t leq where
  order = ord

%hint
public export
InferOrder : {t : Type} -> {spo : t -> t -> Type} -> StrictOrdered t spo => Ordered t (EqOr spo)
InferOrder {t} {spo} @{so} = MkOrdered @{InferPoset} {ord = ord}
  where
    ord : (a,b : t) -> Either (EqOr spo a b) (EqOr spo b a)
    ord  a b with (Strict.order @{so} a b)
     ord a _ | DecEQ Refl = Left  (Left  Refl)
     ord a b | DecLT aLTb = Left  (Right aLTb)
     ord a b | DecGT bLTa = Right (Right bLTa)


public export
(tot : StrictOrdered t lt) => (pre : StrictPreorder t lt) => DecEq t where
  decEq x y = case order @{tot} x y of
    DecEQ x_eq_y => Yes x_eq_y
    DecLT xlty => No $ \x_eq_y => absurd $ irreflexive @{pre} y 
                                         $ replace {p = \u => u `lt` y} x_eq_y xlty
    -- Similarly                                         
    DecGT yltx => No $ \x_eq_y => absurd $ irreflexive @{pre} y
                                         $ replace {p = \u => y `lt` u} x_eq_y yltx
    
