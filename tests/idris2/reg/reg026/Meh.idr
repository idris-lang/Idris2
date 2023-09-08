module Meh

import public Control.WellFounded

public export
interface Argh (rel : a -> a -> Type) where
  argh : (x : a) -> Accessible rel x

data Meh : Nat -> Nat -> Type where

implementation Argh Meh where
  argh x = ?foo
