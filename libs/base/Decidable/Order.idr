module Decidable.Order

import Decidable.Decidable
import Decidable.Equality
import Data.Fin
import Data.Fun
import Data.Rel

%hide Prelude.Equal

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders, Posets, total Orders, Equivalencies, Congruencies
--------------------------------------------------------------------------------

public export
interface ComparisonRelation t where
  constructor CompareWith
  cmp : t -> t -> Type

public export
interface ComparisonRelation t => Preorder t where
  total transitive : (a : t) -> (b : t) -> (c : t) -> a `cmp` b -> b `cmp` c -> a `cmp` c
  total reflexive : (a : t) -> a `cmp` a

public export
interface (Preorder t) => Poset t where
  total antisymmetric : (a : t) -> (b : t) -> a `cmp` b -> b `cmp` a -> a = b

public export
interface (Poset t) => Ordered t where
  total order : (a : t) -> (b : t) -> Either (a `cmp` b) (b `cmp` a)

public export
interface (Preorder t) => Equivalence t where
  total symmetric : (a : t) -> (b : t) -> a `cmp` b -> b `cmp` a

public export
interface (Equivalence t) => Congruence t (f : t -> t) where
  total congruent : (a : t) ->
                    (b : t) ->
                       a  `cmp`    b ->
                    (f a) `cmp` (f b)

public export
minimum : (Ordered t) => t -> t -> t
minimum   x y with (order x y)
  minimum x y | Left  _ = x
  minimum x y | Right _ = y

public export
maximum : (Ordered t) => t -> t -> t
maximum x y with (order x y)
  maximum x y | Left  _ = y
  maximum x y | Right _ = x

--------------------------------------------------------------------------------
-- Syntactic equivalence (=)
--------------------------------------------------------------------------------

public export
[EqualCmp] ComparisonRelation t where
  cmp = Equal

public export
[EqualPreorder] Preorder t using EqualCmp where
  transitive a b c l r = trans l r
  reflexive a = Refl

public export
[EqualEquivalence] Equivalence t using EqualPreorder where
  symmetric a b prf = sym prf

public export
[EqualCongruence] Congruence t f using EqualEquivalence where
  congruent a b eq = cong f eq

