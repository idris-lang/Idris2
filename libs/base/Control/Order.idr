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

--- Derivaties of order-based stuff ---

||| Gives the leftmost of a strongly connex relation among the given two elements, generalisation of `min`.
|||
||| That is, leftmost x y ~ x and leftmost x y ~ y, and `leftmost x y` is either `x` or `y`
public export
leftmost : (0 rel : _) -> StronglyConnex ty rel => ty -> ty -> ty
leftmost rel x y = either (const x) (const y) $ order {rel} x y

||| Gives the rightmost of a strongly connex relation among the given two elements, generalisation of `max`.
|||
||| That is, x ~ rightmost x y and y ~ rightmost x y, and `rightmost x y` is either `x` or `y`
public export
rightmost : (0 rel : _) -> StronglyConnex ty rel => ty -> ty -> ty
rightmost rel x y = either (const y) (const x) $ order {rel} x y

-- properties --

export
leftmostRelL : (0 rel : _) -> Reflexive ty rel => StronglyConnex ty rel => (x, y : ty) -> leftmost rel x y `rel` x
leftmostRelL rel x y with (order {rel} x y)
  _ | Left  _  = reflexive {rel}
  _ | Right yx = yx

export
leftmostRelR : (0 rel : _) -> Reflexive ty rel => StronglyConnex ty rel => (x, y : ty) -> leftmost rel x y `rel` y
leftmostRelR rel x y with (order {rel} x y)
  _ | Left  xy = xy
  _ | Right _  = reflexive {rel}

export
leftmostPreserves : (0 rel : _) -> StronglyConnex ty rel => (x, y : ty) -> Either (leftmost rel x y = x) (leftmost rel x y = y)
leftmostPreserves rel x y with (order {rel} x y)
  _ | Left  _ = Left  Refl
  _ | Right _ = Right Refl

export
leftmostIsRightmostLeft : (0 rel : _) -> StronglyConnex ty rel =>
                          (x, y : ty) ->
                          (z : ty) -> (z `rel` x) -> (z `rel` y) ->
                          (z `rel` leftmost rel x y)
leftmostIsRightmostLeft rel x y z zx zy with (order {rel} x y)
  _ | Left  _ = zx
  _ | Right _ = zy

export
rightmostRelL : (0 rel : _) -> Reflexive ty rel => StronglyConnex ty rel => (x, y : ty) -> x `rel` rightmost rel x y
rightmostRelL rel x y with (order {rel} x y)
  _ | Left  xy = xy
  _ | Right _  = reflexive {rel}

export
rightmostRelR : (0 rel : _) -> Reflexive ty rel => StronglyConnex ty rel => (x, y : ty) -> y `rel` rightmost rel x y
rightmostRelR rel x y with (order {rel} x y)
  _ | Left  _  = reflexive {rel}
  _ | Right yx = yx

export
rightmostPreserves : (0 rel : _) -> StronglyConnex ty rel => (x, y : ty) -> Either (rightmost rel x y = x) (rightmost rel x y = y)
rightmostPreserves rel x y with (order {rel} x y)
  _ | Left  _ = Right Refl
  _ | Right _ = Left  Refl

export
rightmostIsLeftmostRight : (0 rel : _) -> StronglyConnex ty rel =>
                           (x, y : ty) ->
                           (z : ty) -> (x `rel` z) -> (y `rel` z) ->
                           (leftmost rel x y `rel` z)
rightmostIsLeftmostRight rel x y z zx zy with (order {rel} x y)
  _ | Left  _ = zx
  _ | Right _ = zy
