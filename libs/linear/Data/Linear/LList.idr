module Data.Linear.LList

import Data.Linear.Bifunctor
import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat

%default total

public export
data LList : Type -> Type where
  Nil : LList a
  (::) : a -@ LList a -@ LList a

%name LList xs, ys, zs, ws

export
length : Consumable a => LList a -@ LNat
length [] = Zero
length (x :: xs) = consume x `seq` length xs

export
Consumable a => Consumable (LList a) where
  consume [] = ()
  consume (x :: xs) = x `seq` consume xs

export
Duplicable a => Duplicable (LList a) where
  duplicate [] = [[], []]
  duplicate (x :: xs) = (::) <$> duplicate x <*> duplicate xs
