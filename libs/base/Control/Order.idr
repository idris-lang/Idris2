module Control.Order

import Control.Relation

public export
interface (Reflexive ty rel, Transitive ty rel) => Preorder ty rel where

public export
interface (Preorder ty rel, Antisymmetric ty rel) => PartialOrder ty rel where

public export
interface Connex ty rel where
  connex : {x, y : ty} -> Not (x = y) -> Either (rel x y) (rel y x)

public export
interface (PartialOrder ty rel, Connex ty rel) => LinearOrder ty rel where

----------------------------------------

public export
Preorder ty Equal where
