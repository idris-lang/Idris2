module Tricho

data Trichotomy : (eq, lt : a -> a -> Type) -> (a -> a -> Type) where
  LT : {0 x, y : a} -> lt x y -> Trichotomy eq lt x y
  EQ : {0 x, y : a} -> eq x y -> Trichotomy eq lt x x
  GT : {0 x, y : a} -> lt y x -> Trichotomy eq lt x y

interface Trichotomous (a : Type) (eq, lt : a -> a -> Type) where

  trichotomy : (x, y : a) -> Trichotomy eq lt x y
