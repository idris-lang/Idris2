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
interface Preorder t (po : t -> t -> Type) where
  total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  total reflexive : (a : t) -> po a a

public export
interface (Preorder t po) => Poset t (po : t -> t -> Type) where
  total antisymmetric : (a : t) -> (b : t) -> po a b -> po b a -> a = b

public export
interface (Poset t to) => Ordered t (to : t -> t -> Type) where
  total order : (a : t) -> (b : t) -> Either (to a b) (to b a)

public export
interface (Preorder t eq) => Equivalence t (eq : t -> t -> Type) where
  total symmetric : (a : t) -> (b : t) -> eq a b -> eq b a

public export
interface (Equivalence t eq) => Congruence t (f : t -> t) (eq : t -> t -> Type) where
  total congruent : (a : t) ->
                    (b : t) ->
                    eq a b ->
                    eq (f a) (f b)

public export
minimum : (Ordered t to) => t -> t -> t
minimum {to} x y with (order {to} x y)
  minimum {to} x y | Left _ = x
  minimum {to} x y | Right _ = y

public export
maximum : (Ordered t to) => t -> t -> t
maximum {to} x y with (order {to} x y)
  maximum {to} x y | Left _ = y
  maximum {to} x y | Right _ = x

--------------------------------------------------------------------------------
-- Syntactic equivalence (=)
--------------------------------------------------------------------------------

public export
implementation Preorder t Equal where
  transitive a b c l r = trans l r
  reflexive a = Refl

public export
implementation Equivalence t Equal where
  symmetric a b prf = sym prf

public export
implementation Congruence t f Equal where
  congruent a b eq = cong f eq
