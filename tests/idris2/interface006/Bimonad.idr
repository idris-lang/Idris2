module Bimonad

import Biapplicative

infixl 4 >>==

||| Bimonads
||| @p the action of the first Bifunctor component on pairs of objects
||| @q the action of the second Bifunctor component on pairs of objects
interface (Biapplicative p, Biapplicative q) =>
      Bimonad (p : Type -> Type -> Type) (q : Type -> Type -> Type) where

  bijoin : (p (p a b) (q a b), q (p a b) (q a b)) -> (p a b, q a b)
  bijoin p = p >>== (id, id)

  (>>==) : (p a b, q a b) -> ((a -> p c d), (b -> q c d)) -> (p c d, q c d)
  (pab, qab) >>== (f, g) = bijoin $ (bimap f g, bimap f g) <<*>> (pab, qab)

biunit : (Bimonad p q) => a -> b -> (p a b, q a b)
biunit a b = (bipure a b, bipure a b)

implementation Bimonad Pair Pair where
  bijoin = bimap fst snd
