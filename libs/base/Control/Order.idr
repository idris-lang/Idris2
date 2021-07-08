||| An order is a particular kind of binary relation. The order
||| relation is intended to proceed in some direction, though not
||| necessarily with a unique path.
|||
||| Orders are often defined simply as bundles of binary relation
||| properties.
|||
||| A prominent example of an order relation is LTE over Nat.

module Control.Order

import Control.Relation

||| A preorder is reflexive and transitive.
public export
interface (Reflexive ty rel, Transitive ty rel) => Preorder ty rel where

||| A partial order is an antisymmetrics preorder.
public export
interface (Preorder ty rel, Antisymmetric ty rel) => PartialOrder ty rel where

||| A relation is connex if for any two distinct x and y, either x ~ y or y ~ x.
|||
||| This can also be stated as a trichotomy: x ~ y or x = y or y ~ x.
public export
interface Connex ty rel where
  connex : {x, y : ty} -> Not (x = y) -> Either (rel x y) (rel y x)

||| A relation is strongly connex if for any two x and y, either x ~ y or y ~ x.
public export
interface StronglyConnex ty rel where
  order : (x, y : ty) -> Either (rel x y) (rel y x)

||| A linear order is a connex partial order.
public export
interface (PartialOrder ty rel, Connex ty rel) => LinearOrder ty rel where

----------------------------------------

||| Every equivalence relation is a preorder.
public export
[EP] Equivalence ty rel => Preorder ty rel where
