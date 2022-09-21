||| An strict preorder (sometimes known as a quasi-order, or an
||| ordering) is what you get when you remove the diagonal `{(a,b) | a
||| r b , b r a}` from a preorder. For example a < b is an ordering.
||| This module extends base's Control.Order with the strict versions.
||| The interface system seems to struggle a bit with some of the constructions,
||| so I hacked them a bit. Sorry.
module Decidable.Order.Strict

import Control.Relation
import Control.Order
import Decidable.Equality

%default total

public export
interface Irreflexive ty rel where
  irreflexive : {x : ty} -> Not (rel x x)

public export
interface (Transitive ty rel, Irreflexive ty rel) => StrictPreorder  ty rel where

public export
interface Asymmetric ty rel where
  asymmetric : {x, y : ty} -> rel x y -> Not (rel y x)

public export
[SPA] StrictPreorder ty rel => Asymmetric ty rel where
  asymmetric xy yx = irreflexive {rel} $ transitive xy yx

-- We make this completion a record type so that we do not need to name the
-- interface implementations for fear of them interfering with other
-- `Either`-based constructions.

public export
record EqOr {0 t : Type} (spo : Rel t) (a, b : t) where
  constructor MkEqOr
  runEqOr : Either (a = b) (a `spo` b)

public export
Transitive ty rel => Transitive ty (EqOr rel) where

  transitive (MkEqOr (Left  Refl)) bLTEc                 = bLTEc
  transitive aLTEb                 (MkEqOr (Left  Refl)) = aLTEb
  transitive (MkEqOr (Right aLTb)) (MkEqOr (Right bLTc))
    = MkEqOr $ Right $ transitive aLTb bLTc

public export
Reflexive ty (EqOr rel) where
  reflexive = MkEqOr $ Left Refl

public export
Transitive ty rel => Preorder ty (EqOr rel) where

public export
(Irreflexive ty rel, Asymmetric ty rel) => Antisymmetric ty (EqOr rel) where

  antisymmetric (MkEqOr p) (MkEqOr q) = go p q where

    go : {a, b : ty} ->
         Either (a = b) (a `rel` b) ->
         Either (b = a) (b `rel` a) ->
         a = b
    go (Left  Refl) (Left  Refl) = Refl
    go (Left  Refl) (Right bLTa) = absurd (irreflexive {rel} bLTa)
    go (Right aLTb) (Left  Refl) = absurd (irreflexive {rel} aLTb)
    go (Right aLTb) (Right bLTa) = absurd (asymmetric {rel} aLTb bLTa)

public export
(Irreflexive ty rel, Asymmetric ty rel, Transitive ty rel) =>
  PartialOrder ty (EqOr rel) where

public export
data DecOrdering : {lt : t -> t -> Type} -> (a,b : t) -> Type where
  DecLT : forall lt . (a `lt` b) -> DecOrdering {lt = lt} a b
  DecEQ : forall lt . (a  =   b) -> DecOrdering {lt = lt} a b
  DecGT : forall lt . (b `lt` a) -> DecOrdering {lt = lt} a b

public export
interface StrictPreorder t spo => StrictOrdered t spo where
  order : (a,b : t) -> DecOrdering {lt = spo} a b

public export
Connex ty rel => Connex ty (EqOr rel) where
  connex neq = bimap (MkEqOr . Right) (MkEqOr . Right) (connex neq)

public export
(Connex ty rel, DecEq ty) => StronglyConnex ty (EqOr rel) where
  order a b = case decEq a b of
    Yes eq => Left $ MkEqOr (Left eq)
    No neq => connex neq
