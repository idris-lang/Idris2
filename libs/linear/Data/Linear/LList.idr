module Data.Linear.LList

import Data.Linear.Notation
import Data.Linear.LNat

public export
data LList : Type -> Type where
  Nil : LList a
  (::) : a -@ LList a -@ LList a

%name LList xs, ys, zs, ws

export
length : Consumable a => LList a -@ LNat
length [] = Zero
length (x :: xs) = consume x `seq` length xs
